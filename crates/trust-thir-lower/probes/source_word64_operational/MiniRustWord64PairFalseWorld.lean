/- False subjects only, to be rejected during independent proof replay. -/
import MiniRustWord64PairFullCorrespondence
noncomputable section
namespace MiniRustWord64PairFalseWorld
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Step
  MiniRustWord64PairFunction MiniRustWord64PairExecution MiniRustWord64PairReturn
set_option autoImplicit false

def PrematureRetirement : Prop := ∀ (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (action : MR_StackPopAction) (world : List MR_Allocation)
    (retAddr leftAddr rightAddr left right : Nat)
    (retBytes : List MR_AbstractByte) (oldAccesses : List MR_Access)
    (retLength : retBytes.length = 8) (retAligned : retAddr % 8 = 0)
    (leftAligned : leftAddr % 8 = 0) (rightAligned : rightAddr % 8 = 0)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64),
    MRf.Machine.step (fuel + 50)
      (active base caller (localFrame world retAddr leftAddr rightAddr action 0)
        (cells world retAddr leftAddr rightAddr retBytes left right oldAccesses)) =
    oneThreadChoice (.ok (), active base caller
      (localFrame world retAddr leftAddr rightAddr action 1)
      (MiniRustWord64PairReturn.retiredCells world retAddr leftAddr rightAddr ((left + right) % modulus 64) left right
        [⟨.Load, .None, Int.ofNat leftAddr, 8⟩, ⟨.Load, .None, Int.ofNat rightAddr, 8⟩,
          ⟨.Store, .None, Int.ofNat retAddr, 8⟩]))

end MiniRustWord64PairFalseWorld
