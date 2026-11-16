/- A separately named actual generated AST. The immutable Returning entry
   remains an exact UB control. This entry terminates with supported Exit. -/
import MiniRustProgramExit
set_option autoImplicit false
noncomputable section
namespace MiniRustU64ExitProgram
open SemR MiniRustU64Function MiniRustU64Program
open MiniRustU64ProgramTyping
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def exitTerm : MR_Terminator := .Intrinsic .Exit [] (.Local ⟨0⟩) none

def exitBlock : MR_BasicBlock :=
  { statements := [], terminator := exitTerm, kind := .Regular }

/-- Actual C/unit entry, same scalar call block, separately named Exit block. -/
def exitEntry (input : Nat) : MR_Function :=
  { locals := [(⟨0⟩, unitTy), (⟨1⟩, .Int (mrIntTy false .u64))]
    args := [], ret := ⟨0⟩, calling_convention := .C
    blocks := [(⟨0⟩, callBlock input), (⟨1⟩, exitBlock)]
    start := ⟨0⟩ }

def exitProgram (literal input : Nat) : MR_Program :=
  { functions := [(⟨0⟩, exitEntry input), (⟨1⟩, function literal)]
    start := ⟨0⟩, globals := [], traits := [], vtables := [] }

theorem entry_locals (input : Nat) :
    (exitEntry input).locals = [(⟨0⟩, unitTy), (⟨1⟩, .Int (mrIntTy false .u64))] := rfl
theorem entry_args (input : Nat) : (exitEntry input).args = [] := rfl
theorem entry_ret (input : Nat) : (exitEntry input).ret = ⟨0⟩ := rfl
theorem entry_start (input : Nat) : (exitEntry input).start = ⟨0⟩ := rfl
theorem entry_blocks (input : Nat) :
    (exitEntry input).blocks = [(⟨0⟩, callBlock input), (⟨1⟩, exitBlock)] := rfl

theorem function_pointer (fuel literal input : Nat) :
    MRf.Constant.check_wf (fuel + 2) (.FnPointer ⟨1⟩) (.Ptr .FnPtr)
      (exitProgram literal input) = .ok (.ok ()) := rfl

theorem pointer_expression (fuel literal input : Nat) (locals : List (MR_LocalName × MR_Type)) :
    MRf.ValueExpr.check_wf (fuel + 20) (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr))
      locals (exitProgram literal input) = .ok (.ok (.Ptr .FnPtr)) := by
  apply constant_expression (fuel + 18)
  · exact pointer_type (fuel + 3) (exitProgram literal input)
  · exact function_pointer (fuel + 17) literal input

theorem result_place (fuel input : Nat) (prog : MR_Program) :
    MRf.PlaceExpr.check_wf (fuel + 2) (.Local ⟨1⟩) (exitEntry input).locals prog =
      .ok (.ok (.Int (mrIntTy false .u64))) := rfl

theorem result_storage (fuel input : Nat) (prog : MR_Program) :
    MRf.Statement.check_wf (fuel + 2) (.StorageLive ⟨1⟩) (exitEntry input) prog = .ok (.ok ()) := rfl

theorem next_block (fuel input : Nat) :
    MRf.Function.check_next_block (fuel + 2) (exitEntry input) .Regular ⟨1⟩ = .ok (.ok ()) := rfl

theorem exit_place (fuel input : Nat) (prog : MR_Program) :
    MRf.PlaceExpr.check_wf (fuel + 2) (.Local ⟨0⟩) (exitEntry input).locals prog = .ok (.ok unitTy) := rfl

/-- The actual generated Intrinsic checker checks its sized result place and
    arguments. Exit with an existing unit result place and no successor is
    supported by that checker; no custom validator is substituted. -/
theorem exit_wellformed (fuel input : Nat) (prog : MR_Program) :
    MRf.Terminator.check_wf (fuel + 20) exitTerm .Regular (exitEntry input) prog = .ok (.ok ()) := by
  have placeChecked (k : Nat) := exit_place k input prog
  simp only [exitTerm, MRf.Terminator.check_wf, placeChecked, MiniRustU64Program.unit_layout,
    MRf.LayoutStrategy.is_sized, MRf.fn.ensure_wf, SLoop.forS, SOut.bind, SBool.not]

theorem call_wellformed (fuel literal input : Nat) (inputValid : input < modulus 64) :
    MRf.Terminator.check_wf (fuel + 40) (callTerm input) .Regular
      (exitEntry input) (exitProgram literal input) = .ok (.ok ()) := by
  have ptrChecked (k : Nat) (locals : List (MR_LocalName × MR_Type)) :=
    pointer_expression k literal input locals
  have argChecked (k : Nat) (locals : List (MR_LocalName × MR_Type)) :=
    u64_argument k input locals (exitProgram literal input) inputValid
  have placeChecked (k : Nat) := result_place k input (exitProgram literal input)
  have nextChecked (k : Nat) := next_block k input
  unfold callTerm
  simp only [MRf.Terminator.check_wf, ptrChecked, argChecked, placeChecked, nextChecked,
    MiniRustU64Function.layout_u64, SBool.not, SLoop.forS, SOut.bind, MRf.fn.ensure_wf,
    MRf.LayoutStrategy.is_sized]

theorem entry_wellformed (fuel literal input : Nat) (inputValid : input < modulus 64) :
    MRf.Function.check_wf (fuel + 64) (exitEntry input) (exitProgram literal input) = .ok (.ok ()) := by
  have callChecked (k : Nat) := call_wellformed k literal input inputValid
  have storageChecked (k : Nat) := result_storage k input (exitProgram literal input)
  have exitChecked (k : Nat) := exit_wellformed k input (exitProgram literal input)
  have u64Checked (k : Nat) := u64_type k (exitProgram literal input)
  have unitChecked (k : Nat) := unit_type k (exitProgram literal input)
  simp only [MRf.Function.check_wf, entry_locals, entry_args, entry_ret, entry_blocks,
    callBlock, exitBlock, callChecked, storageChecked, exitChecked, u64Checked, unitChecked,
    MiniRustU64Function.layout_u64, MiniRustU64Program.unit_layout, SBool.not, SList.appendL,
    SList.push, SLoop.forS, SMap.contains_key, SMap.get, SMap.getL, SMap.values, SOption.is_some,
    SOut.bind, SRes.is_err, SSet.contains, SSet.try_insert, MR_LocalName.beq, MRf.fn.ensure_wf,
    MRf.LayoutStrategy.is_sized]

theorem program_functions (literal input : Nat) :
    (exitProgram literal input).functions = [(⟨0⟩, exitEntry input), (⟨1⟩, function literal)] := rfl
theorem program_start (literal input : Nat) : (exitProgram literal input).start = ⟨0⟩ := rfl
theorem program_globals (literal input : Nat) : (exitProgram literal input).globals = [] := rfl
theorem program_traits (literal input : Nat) : (exitProgram literal input).traits = [] := rfl
theorem program_vtables (literal input : Nat) : (exitProgram literal input).vtables = [] := rfl
theorem entry_convention (input : Nat) : (exitEntry input).calling_convention = .C := rfl

/-- Universal generated well-formedness, before allocation or execution. -/
theorem program_wellformed (fuel literal input : Nat)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    MRf.Program.check_wf (fuel + 80) (exitProgram literal input) = .ok (.ok ()) := by
  have entryChecked (k : Nat) := entry_wellformed k literal input inputValid
  have scalarChecked (k : Nat) := scalar_wellformed k literal (exitProgram literal input) literalValid
  simp only [MRf.Program.check_wf, program_functions, program_start, program_globals, program_traits,
    program_vtables, entry_convention, entry_locals, entry_ret, entry_args, entryChecked, scalarChecked,
    MiniRustU64Program.unit_layout, MiniRustU64ProgramTyping.unit_layout_equal, MR_CallingConvention.beq,
    MR_FnName.beq, SBool.not, SList.len, SLoop.forS, SMap.get, SMap.getL, SMap.index_at, SMap.values,
    SOption.unwrap, SOut.bind, MR_LocalName.beq, MRf.fn.ensure_wf, SInt.beq]
  rfl

#print axioms program_wellformed
end MiniRustU64ExitProgram
