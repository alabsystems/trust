-- Copyright 2026 Andrew Yates | Apache-2.0
import CAtomicDropSyntax
import TrustIr.Semantics.Atomic

/-!
Lean-owned candidate production from a checked COMPLETE source fragment.
This uses existing canonical memory/atomic operations rather than a second
runtime evaluator. It is NOT a C11 translation-correctness theorem: the actual
macro binding, object/header layout, C typing, source/TU attachment, atomic
interference and rights/NoUB simulation remain required. IR906's atomics are
single-threaded SC and its fence is pure; no C11 acquire/release conclusion is
licensed. Temporary SSA locals/count also preclude whole-world equality.
-/
namespace CAtomicDropCandidate
open TrustIr CAtomicDropSyntax

private def readU32 (id : ValueId) : Sem Int := do
  let value ← Sem.lookupValue id
  match value with
  | .int 32 n => pure n
  | _ => Sem.throwTypeError "C atomic-drop proposal: expected UInt32"

/-- Proposal only: preserve the actual branch and event sequence, including
both reads, returned OLD RMW value and the last-reference acquire fence. -/
def program (threshold : Nat) (headerPointer : ValueId) : Sem Bool := do
  let observed ← semAtomicLoad .U32 headerPointer .Relaxed
  let initial ← readU32 observed
  if initial ≥ Int.ofNat threshold then return false
  let one ← Sem.bindFresh (.int 32 1)
  let old ← semAtomicRMW .Sub .U32 headerPointer one .Release
  let previous ← readU32 old
  if previous != 0 then return false
  semFence .Acquire
  return true

/-- The numeric threshold is untrusted binding DATA; this does not infer it
from a familiar macro name. Full-TU checked binding remains separately owed. -/
def propose (source : List UInt8) (proposal : Proposal) (threshold : Nat)
    (headerPointer : ValueId) : Option (Sem Bool) :=
  if check source proposal then some (program threshold headerPointer) else none

theorem unsupported_source_refuses (source : List UInt8) (proposal : Proposal)
    (threshold : Nat) (pointer : ValueId) (bad : check source proposal = false) :
    propose source proposal threshold pointer = none := by
  simp [propose, bad]

theorem checked_source_proposes (source : List UInt8) (proposal : Proposal)
    (threshold : Nat) (pointer : ValueId) (accepted : check source proposal = true) :
    propose source proposal threshold pointer = some (program threshold pointer) := by
  simp [propose, accepted]

#print axioms unsupported_source_refuses
#print axioms checked_source_proposes
end CAtomicDropCandidate
