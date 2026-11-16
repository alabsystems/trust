/- Actual two-argument entry plus body, preserving all five choice layers.
   Model theorem only: no Rust source, ABI or compiler admission authority. -/
import MiniRustWord64PairAllocatedCall
import MiniRustWord64PairRun
noncomputable section
namespace MiniRustWord64PairEntryRun
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64AllocatedCall MiniRustAllocate8Safety
  MiniRustWord64PairFunction MiniRustWord64PairExecution MiniRustWord64PairReturn
  MiniRustWord64PairRun
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def afterEntry (fuel : Nat) (result : SRes MR_TerminationInfo Unit × MR_Machine) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match result with
  | (.ok _, machine) => twoSteps fuel machine
  | (.err error, machine) => .ok (.err error, machine)

def enterAndRun (fuel left right : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access) :=
  (MRf.Machine.eval_call (fuel + 21)
    (single base [caller] ⟨⟨callerWorld before after callerAddr callerBytes, ()⟩, accesses⟩)
    MiniRustWord64PairFunction.function .Rust
    [(.Int (Int.ofNat left), .Int (mrIntTy false .u64)),
     (.Int (Int.ofNat right), .Int (mrIntTy false .u64))]
    (place (ptr before.length (Int.ofNat callerAddr)), .Int (mrIntTy false .u64))
    (some next) none).bind (afterEntry (fuel + 50))

def fullTree (left right : Nat) (base : MR_Machine) (caller : MR_StackFrame)
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
          ((left + right) % modulus 64) left right)))))

/-- Full entry/body world equality without a successful-call premise. -/
theorem full_tree_exact (fuel left right : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (next : MR_BbName) (before after : List MR_Allocation) (callerAddr : Nat)
    (callerBytes : List MR_AbstractByte) (accesses : List MR_Access)
    (callerLength : callerBytes.length = 8) (callerAligned : callerAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    enterAndRun fuel left right base caller next before after callerAddr callerBytes accesses =
      fullTree left right base caller next before after callerAddr callerBytes := by
  unfold enterAndRun
  rw [MiniRustWord64PairAllocatedCall.call_tree_exact fuel left right _ accesses base caller
    _ _ _ leftValid rightValid]
  unfold MiniRustWord64PairAllocatedCall.callTree fullTree
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes)))
  funext retIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes ++
      [slot (Int.ofNat (address retIndex)) uninit8])))
  funext leftIndex
  rw [selected_bind]
  apply congrArg (selectedChoice (Int.ofNat (modulus 64))
    (allocationAllowed (callerWorld before after callerAddr callerBytes ++
      [slot (Int.ofNat (address retIndex)) uninit8,
       slot (Int.ofNat (address leftIndex)) uninit8])))
  funext rightIndex
  simp only [SOut.bind_ok', afterEntry]
  exact two_steps_exact fuel base caller left right next before after callerAddr
    (address retIndex) (address leftIndex) (address rightIndex) callerBytes uninit8 _
    callerLength uninit8_length callerAligned (address_aligned _) (address_aligned _)
    (address_aligned _) leftValid rightValid

#print axioms full_tree_exact
end MiniRustWord64PairEntryRun
