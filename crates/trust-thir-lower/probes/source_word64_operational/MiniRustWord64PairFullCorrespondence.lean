/- Exact retained IR execution indexes the complete actual MiniRust function
   world, including entry allocations. This does not authenticate Rust source. -/
import MiniRustWord64PairAvailability
import SemRWord64Pair
noncomputable section
namespace MiniRustWord64PairFullCorrespondence
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64AllocatedCall MiniRustAllocate8Safety
  MiniRustWord64PairRun MiniRustWord64PairEntryRun
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def observedTree (value left right : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) : SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes)) (fun retIndex =>
    selectedChoice (Int.ofNat (modulus 64))
      (allocationAllowed (callerWorld before after callerAddr callerBytes ++
        [slot (Int.ofNat (address retIndex)) uninit8])) (fun leftIndex =>
      selectedChoice (Int.ofNat (modulus 64))
        (allocationAllowed (callerWorld before after callerAddr callerBytes ++
          [slot (Int.ofNat (address retIndex)) uninit8,
           slot (Int.ofNat (address leftIndex)) uninit8])) (fun rightIndex =>
        scheduled (oneThreadChoice (.ok (), exitState base caller next before after
          callerAddr (address retIndex) (address leftIndex) (address rightIndex)
          value left right)))))

theorem original_function_correspondence (fuel left right depth : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    ∃ value : Nat,
      runBlob SemRWord64Pair.originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
        .ok (.ret [.int .u64 value]) ∧
    enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses =
      observedTree value left right base caller next before after callerAddr callerBytes := by
  refine ⟨(left + right) % modulus 64,
    SemRWord64Pair.original_returns left right depth leftValid rightValid, ?_⟩
  exact full_tree_exact fuel left right base caller next before after callerAddr callerBytes accesses
    callerLength callerAligned leftValid rightValid

/-- Deliberately false world subjects for unchanged-proof replay controls.
    Swapped argument slots matter even though scalar addition commutes. -/
def WrongArgumentBinding : Prop := ∀ (fuel left right depth : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64),
    ∃ value : Nat,
      runBlob SemRWord64Pair.originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
        .ok (.ret [.int .u64 value]) ∧
    enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses =
      observedTree value right left base caller next before after callerAddr callerBytes

def ReturningInput : Prop := ∀ (fuel left right depth : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64),
    ∃ value : Nat,
      runBlob SemRWord64Pair.originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
        .ok (.ret [.int .u64 value]) ∧
    enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses =
      observedTree left left right base caller next before after callerAddr callerBytes

def WrongArithmetic : Prop := ∀ (fuel left right depth : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64),
    ∃ value : Nat,
      runBlob SemRWord64Pair.originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
        .ok (.ret [.int .u64 value]) ∧
    enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses =
      observedTree ((left + left) % modulus 64) left right base caller next before after callerAddr callerBytes

def AlteredOutsideWorld : Prop := ∀ (fuel left right depth : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64),
    ∃ value : Nat,
      runBlob SemRWord64Pair.originalBytes 0 [.int .u64 left, .int .u64 right] 2 depth =
        .ok (.ret [.int .u64 value]) ∧
    enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses =
      observedTree value left right base caller next [] after callerAddr callerBytes

#print axioms original_function_correspondence
end MiniRustWord64PairFullCorrespondence
