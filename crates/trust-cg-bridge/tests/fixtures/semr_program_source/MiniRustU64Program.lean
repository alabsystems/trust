/- Real generated program startup for the decoded scalar-function model.
   The C/unit entry allocates its own caller result slot and calls the Rust
   function. It is a model program, not an asserted Rust frontend translation. -/
import MiniRustAllocate
import MiniRustU64ScalarCorrespondence

noncomputable section
namespace MiniRustU64Program
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Entry
  MiniRustU64Call MiniRustU64AllocatedCall MiniRustU64Run
  MiniRustU64Correspondence MiniRustU64Availability MiniRustAllocate
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def unitTy : MR_Type := .Tuple [] ⟨0, 1, none⟩ none

def callTerm (input : Nat) : MR_Terminator :=
  .Call (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr)) .Rust
    [.ByValue (.Constant (.Int (Int.ofNat input)) (.Int (mrIntTy false .u64)))]
    (.Local ⟨1⟩) (some ⟨1⟩) none

def callBlock (input : Nat) : MR_BasicBlock :=
  { statements := [.StorageLive ⟨1⟩], terminator := callTerm input, kind := .Regular }

def returnBlock : MR_BasicBlock :=
  { statements := [], terminator := .Return, kind := .Regular }

/-- This is an actual generated AST, including StorageLive and the complete
    function-pointer call. Startup and the caller frame are not premises. -/
def entry (input : Nat) : MR_Function :=
  { locals := [(⟨0⟩, unitTy), (⟨1⟩, .Int (mrIntTy false .u64))]
    args := [], ret := ⟨0⟩, calling_convention := .C
    blocks := [(⟨0⟩, callBlock input), (⟨1⟩, returnBlock)]
    start := ⟨0⟩ }

theorem entry_locals (input : Nat) :
    (entry input).locals = [(⟨0⟩, unitTy), (⟨1⟩, .Int (mrIntTy false .u64))] := rfl
theorem entry_args (input : Nat) : (entry input).args = [] := rfl
theorem entry_ret (input : Nat) : (entry input).ret = ⟨0⟩ := rfl
theorem entry_start (input : Nat) : (entry input).start = ⟨0⟩ := rfl
theorem entry_blocks (input : Nat) :
    (entry input).blocks = [(⟨0⟩, callBlock input), (⟨1⟩, returnBlock)] := rfl

def program (literal input : Nat) : MR_Program :=
  { functions := [(⟨0⟩, entry input), (⟨1⟩, function literal)]
    start := ⟨0⟩, globals := [], traits := [], vtables := [] }

theorem unit_type (fuel : Nat) : MRf.fn.unit_type (fuel + 1) = SOut.ok unitTy := rfl

theorem unit_layout (fuel : Nat) :
    MRf.Type.layout (fuel + 4) unitTy = SOut.ok (.Sized 0 1) := rfl

/-- A real generated program well-formedness execution, before any allocation
    or startup theorem. The open laws below will quantify over all full64 data. -/
theorem program_wellformed_control (fuel : Nat) :
    MRf.Program.check_wf (fuel + 80) (program 7 3) = SOut.ok (.ok ()) := by
  rfl

end MiniRustU64Program
