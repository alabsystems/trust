-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ByteMemory
import TrustIr.Semantics.ARC

/-!
A proposed representation relation at the canonical TrustIR memory boundary.
The offset/size match the retained Clean C header's UInt64 box, but this file
DOES NOT prove that C allocation/boxing/FFI implements this relation. In
particular it supplies no external-call meaning, source theorem, or admission.
The conclusions execute the existing canonical memory operations, not a new
runtime evaluator. Preconditions describe allocation/bytes, never a successful
execution. The complete input world is retained by the held-value loads.
-/
namespace BoxedWord64
open TrustIr

/-- The initialized payload of a live, aligned 16-byte-or-larger Clean box.
Header/reference-count and physical C-source correspondence are separate.
The actual unsigned word is bounded rather than normalized silently. -/
structure Payload (s : MachineState) (cell : Allocation) (word : Nat) : Prop where
  lookup : s.memory.lookup cell.id = some cell
  live : cell.alive = true
  origin : cell.origin = .cleanHeap
  room : 16 ≤ cell.size
  aligned : (cell.base + 8) % 8 = 0
  initialized : s.memory.readBytes (cell.base + 8) 8 =
    some (encodeIntBytes (Int.ofNat word) 8)
  bounded : word < 2^64

private theorem run_get (s : MachineState) : Sem.run Sem.getState s = .ok (s, s) := rfl

private theorem payload_decode (memory : Memory) (word : Nat) (bounded : word < 2^64) :
    decodeMemoryAt .le64 memory .U64 (encodeIntBytes (Int.ofNat word) 8) =
      .ok (.int 64 (Int.ofNat word)) := by
  have len : (encodeIntBytes (Int.ofNat word) 8).length = 8 :=
    encodeIntBytes_length _ _
  simp only [decodeMemoryAt, decodeValueAt, decodeImageAt, Ty.isFloat,
    decodeValue, len, BEq.beq, decide_true, ite_true,
    decode_encode_address word bounded, Memory.resolveDecoded]
  rfl

/-- A canonical strict payload load returns the represented word and the
EXACT original state, including arbitrary other allocations and choice inputs. -/
theorem payload_load (s : MachineState) (cell : Allocation) (word : Nat)
    (rep : Payload s cell word) :
    (semLoadValueUsing (fun memory bytes => decodeMemoryAt .le64 memory .U64 bytes)
      .U64 (.ptr (cell.base + 8) (some cell.id)) true none .le64).run s =
      .ok (.int 64 (Int.ofNat word), s) := by
  have lower : ¬ cell.base + 8 < cell.base := Nat.not_lt.mpr (Nat.le_add_right _ _)
  simp [semLoadValueUsing, Sem.rejectPartial, Sem.expectPointer,
    Ty.byteSizeFor, Ty.byteSize, Sem.accessAlign, Sem.declaredOrNaturalAlign,
    Ty.byteAlignFor, Ty.byteAlign, isPow2, isPow2Fuel, Sem.checkedAccess,
    Sem.checkTargetRange, run_get, Sem.run_bind, rep.lookup, rep.live, rep.aligned,
    lower, Nat.not_lt.mpr rep.room,
    rep.initialized,
    Except.bind]
  have decoded := payload_decode s.memory word rep.bounded
  simp only [Int.ofNat_eq_natCast] at decoded
  rw [decoded]
  rfl

/-- Reads performed before ownership consumption preserve both payloads,
including aliasing: no distinct-cell premise is imposed. This corresponds to
the existing boxed-wrapper ordering, not to an external-call success claim. -/
theorem both_payloads_before_release (s : MachineState) (left right : Allocation)
    (a b : Nat) (ha : Payload s left a) (hb : Payload s right b) :
    ((do
      let a' ← semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
        .U64 (.ptr (left.base + 8) (some left.id)) true
      let b' ← semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
        .U64 (.ptr (right.base + 8) (some right.id)) true
      pure (a', b')) : Sem (Value × Value)).run s =
        .ok ((.int 64 (Int.ofNat a), .int 64 (Int.ofNat b)), s) := by
  simp only [Sem.run_bind, payload_load s left a ha]
  simp only [Except.bind]
  rw [payload_load s right b hb]
  rfl

/-- Nonvacuity for EVERY bounded raw word, using the canonical byte store. -/
def witnessCell : Allocation :=
  { id := ⟨0⟩, base := 16, size := 16, alive := true,
    origin := .cleanHeap, requested := 16 }

def witnessState (word : Nat) : MachineState :=
  { MachineState.empty with memory := ({ Memory.empty with allocations := [witnessCell], nextAddr := 32, nextAllocId := 1 }).writeBytes 24 (encodeIntBytes (Int.ofNat word) 8) }

theorem witness_represents (word : Nat) (bounded : word < 2^64) :
    Payload (witnessState word) witnessCell word := by
  constructor
  · simp [witnessState, witnessCell, Memory.writeBytes, Memory.lookup]
  · rfl
  · rfl
  · decide
  · decide
  · change (({ Memory.empty with allocations := [witnessCell], nextAddr := 32, nextAllocId := 1 }).writeBytes 24 (encodeIntBytes (Int.ofNat word) 8)).readBytes 24 8 = _
    simpa only [encodeIntBytes_length] using
      (writeBytes_readBytes_general
        ({ Memory.empty with allocations := [witnessCell], nextAddr := 32, nextAllocId := 1 })
        24 (encodeIntBytes (Int.ofNat word) 8))
  · exact bounded

/-- A fixed payload cannot certify two different unsigned words. -/
theorem represented_word_unique (s : MachineState) (cell : Allocation) (a b : Nat)
    (ha : Payload s cell a) (hb : Payload s cell b) : a = b := by
  have same := payload_load s cell b hb
  rw [payload_load s cell a ha] at same
  cases same
  rfl

/-- The existing canonical reader rejects an unowned pointer before any read. -/
theorem missing_provenance_refuses (s : MachineState) :
    (semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
      .U64 (.ptr 24 none) true).run s =
        .error (.ub "Load: pointer value 24 has no allocation provenance") := by
  rfl

/-- Actual canonical bounds checking rejects a payload outside its allocation. -/
theorem short_allocation_refuses (word : Nat) :
    (semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
      .U64 (.ptr 24 (some ⟨0⟩)) true).run
      { witnessState word with memory := { (witnessState word).memory with
        allocations := [{ witnessCell with size := 8 }] } } =
        .error (.ub "Load: access is out of bounds") := by rfl

/-- A deallocated box is not a representation, even with unchanged bytes. -/
theorem freed_allocation_refuses (word : Nat) :
    (semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
      .U64 (.ptr 24 (some ⟨0⟩)) true).run
      { witnessState word with memory := { (witnessState word).memory with
        allocations := [{ witnessCell with alive := false }] } } =
        .error (.ub "Load: use after dealloc") := by rfl

/-- Strict reads cannot treat an allocated but unwritten payload as zero. -/
theorem uninitialized_payload_refuses :
    (semLoadValueUsing (fun m bs => decodeMemoryAt .le64 m .U64 bs)
      .U64 (.ptr 24 (some ⟨0⟩)) true).run
      { MachineState.empty with memory := { Memory.empty with allocations := [witnessCell] } } =
        .error (.ub "Load: reading uninitialized memory") := by rfl

#print axioms short_allocation_refuses
#print axioms freed_allocation_refuses
#print axioms uninitialized_payload_refuses

#print axioms payload_load
#print axioms both_payloads_before_release
#print axioms witness_represents
#print axioms represented_word_unique
#print axioms missing_provenance_refuses

end BoxedWord64
