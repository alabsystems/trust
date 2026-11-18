-- Copyright 2026 Andrew Yates | Apache-2.0
import BoxedWord64ARCWrapper
import BoxedWord64ARCControls

/-!
Necessary representation arithmetic for the ordinary, nonsticky Clean header.
This executes canonical ARC, NOT the C functions. Header constants below are
source-observation DATA from clean_runtime.h at Clean 388fc7b62806. There is no
C parser/atomic-memory soundness theorem or source attachment in this file.
In particular a numeric header never establishes individual ownership rights.
-/
namespace BoxedWord64.HeaderEncoding
open TrustIr

def dropThreshold : Nat := 0xE0000000
def incrementThreshold : Nat := 0xF0000000
def modulus : Nat := 0x100000000

def references (header : Nat) : Nat := header + 1

/-- The physical header observation is separate DATA. The actual canonical
payload, permission and supplied logical reference budget remain necessary. -/
structure Ordinary (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word header : Nat) : Prop where
  canonical : ArcPayload s operand cell word (references header)
  nonsticky : header < dropThreshold

theorem ordinary_positive (header : Nat) : 0 < references header :=
  Nat.zero_lt_succ header

theorem distinct_thresholds : dropThreshold < incrementThreshold ∧
    incrementThreshold < modulus := by decide

/-- A shared ordinary header h+1 represents h+2 logical references. Its
canonical release represents header h; the payload/ambient state is retained. -/
theorem shared_release (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word h : Nat) (rep : Ordinary s operand cell word (h + 1)) :
    Sem.run (semRelease operand) s = .ok ((), countState s cell.id (references h)) ∧
    Ordinary (countState s cell.id (references h)) operand cell word h := by
  have run := release_shared_runs s operand cell word h rep.canonical
  refine ⟨run, countState_arcPayload s operand cell word _ _ rep.canonical, ?_⟩
  exact Nat.lt_trans (Nat.lt_succ_self h) rep.nonsticky

/-- Staying below the drop threshold is required for another ordinary
representation. The larger C increment threshold is deliberately not substituted. -/
theorem retain_ordinary (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word h : Nat) (rep : Ordinary s operand cell word h)
    (room : h + 1 < dropThreshold) :
    Sem.run (semRetain operand) s = .ok ((), countState s cell.id (references (h + 1))) ∧
    Ordinary (countState s cell.id (references (h + 1))) operand cell word (h + 1) := by
  refine ⟨retain_runs s operand cell word h rep.canonical,
    countState_arcPayload s operand cell word _ _ rep.canonical, room⟩

/-- Header zero is one reference, so canonical last release invalidates the
payload. The C atomic fetch-sub's transient u32 wrap is not a live postheader. -/
theorem last_release (s : MachineState) (operand : ValueId) (cell : Allocation)
    (word : Nat) (rep : Ordinary s operand cell word 0) :
    Sem.run (semRelease operand) s = .ok ((), lastReleaseState s cell.id) :=
  release_last_runs s operand cell word rep.canonical

theorem zero_sub_wrap : (0 + modulus - 1) % modulus = 0xFFFFFFFF := by decide

/-- Canonical nonfinal updates do not write header bytes at all. Thus their
whole-memory equality must not be asserted for the physical C atomic write. -/
theorem canonical_count_memory_frame (s : MachineState) (id : AllocId) (n : Nat) :
    (countState s id n).memory = s.memory := rfl

/-- The source sticky-drop boundary lies outside the ordinary representation. -/
theorem sticky_is_not_ordinary (s : MachineState) (operand : ValueId)
    (cell : Allocation) (word header : Nat) (sticky : dropThreshold ≤ header) :
    ¬ Ordinary s operand cell word header := by
  intro rep
  exact Nat.not_lt_of_ge sticky rep.nonsticky

/-- This band is frozen for C drop but below its increment cutoff: the two
source guards cannot be merged into one threshold. This is arithmetic DATA. -/
theorem asymmetric_band : dropThreshold ≤ 0xE8000000 ∧
    0xE8000000 < incrementThreshold := by decide

/-- Numeric representation is inhabited for every bounded word and ordinary
header, in the existing nonempty canonical witness world. No physical C heap
or individual source-owned reference is constructed by this witness. -/
theorem ordinary_witness (word header : Nat) (bounded : word < 2^64)
    (ordinary : header < dropThreshold) :
    Ordinary (ambientWitnessState word (references header)) ⟨0⟩ witnessCell word header ∧
    Ordinary (ambientWitnessState word (references header)) ⟨1⟩ witnessCell word header := by
  have rep := ambient_witness_represents word (references header) bounded
  exact ⟨⟨rep.1, ordinary⟩, ⟨rep.2, ordinary⟩⟩

/-- Two owned aliases need header one, not a fresh header-zero observation. -/
theorem alias_header_one (s : MachineState) (left right : ValueId)
    (cell : Allocation) (word : Nat)
    (a : Ordinary s left cell word 1) (b : Ordinary s right cell word 1) :
    Sem.run (do semRelease left; semRelease right) s =
      .ok ((), lastReleaseState s cell.id) :=
  alias_two_releases s left right cell word a.canonical b.canonical

#print axioms shared_release
#print axioms retain_ordinary
#print axioms last_release
#print axioms ordinary_witness
#print axioms alias_header_one
end BoxedWord64.HeaderEncoding
