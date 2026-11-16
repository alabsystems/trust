/- Full64 well-formedness of the actual startup/call program.
   Value-bearing Constant checks are proved first, then substituted into the
   unchanged generated structural checker. No successful startup is a premise. -/
import MiniRustU64Program

noncomputable section
namespace MiniRustU64ProgramTyping
open SemR MiniRustU64Function MiniRustU64Program
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem u64_constant (fuel value : Nat) (prog : MR_Program)
    (valid : value < modulus 64) :
    MRf.Constant.check_wf (fuel + 2) (.Int (Int.ofNat value))
      (.Int (mrIntTy false .u64)) prog = SOut.ok (.ok ()) := by
  simp only [MRf.Constant.check_wf]
  rw [mr_can_represent fuel false .u64 (Int.ofNat value)]
  simp only [IntTy.bits]
  rw [inRange_nat 64 value valid]
  rfl

theorem function_pointer (fuel literal input : Nat) :
    MRf.Constant.check_wf (fuel + 2) (.FnPointer ⟨1⟩) (.Ptr .FnPtr)
      (program literal input) = SOut.ok (.ok ()) := by
  rfl

theorem u64_type (fuel : Nat) (prog : MR_Program) :
    MRf.Type.check_wf (fuel + 16) (.Int (mrIntTy false .u64)) prog = SOut.ok (.ok ()) := rfl

theorem unit_type (fuel : Nat) (prog : MR_Program) :
    MRf.Type.check_wf (fuel + 16) unitTy prog = SOut.ok (.ok ()) := rfl

theorem pointer_type (fuel : Nat) (prog : MR_Program) :
    MRf.Type.check_wf (fuel + 16) (.Ptr .FnPtr) prog = SOut.ok (.ok ()) := rfl

/-- Expose only the selected constructor, leaving the recursive callback
    packet intact. These two well-formedness premises are proved at each use. -/
theorem constant_expression (fuel : Nat) (value : MR_Constant) (ty : MR_Type)
    (locals : List (MR_LocalName × MR_Type)) (prog : MR_Program)
    (typed : MRf.Type.check_wf (fuel + 1) ty prog = SOut.ok (.ok ()))
    (checked : MRf.Constant.check_wf (fuel + 1) value ty prog = SOut.ok (.ok ())) :
    MRf.ValueExpr.check_wf (fuel + 2) (.Constant value ty) locals prog =
      SOut.ok (.ok ty) := by
  change MRf.ValueExpr.check_wf_open (MR_rec_38.tie (fuel + 1)) (fuel + 2)
    (.Constant value ty) locals prog = _
  simp only [MRf.ValueExpr.check_wf_open]
  rw [typed]
  simp only [SOut.bind_ok']
  rw [checked]
  rfl

theorem u64_expression (fuel value : Nat) (locals : List (MR_LocalName × MR_Type))
    (prog : MR_Program) (valid : value < modulus 64) :
    MRf.ValueExpr.check_wf (fuel + 20)
      (.Constant (.Int (Int.ofNat value)) (.Int (mrIntTy false .u64))) locals prog =
        SOut.ok (.ok (.Int (mrIntTy false .u64))) := by
  apply constant_expression (fuel + 18)
  · exact u64_type (fuel + 3) prog
  · exact u64_constant (fuel + 17) value prog valid

theorem pointer_expression (fuel literal input : Nat)
    (locals : List (MR_LocalName × MR_Type)) :
    MRf.ValueExpr.check_wf (fuel + 20) (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr))
      locals (program literal input) = SOut.ok (.ok (.Ptr .FnPtr)) := by
  apply constant_expression (fuel + 18)
  · exact pointer_type (fuel + 3) (program literal input)
  · exact function_pointer (fuel + 17) literal input

theorem u64_argument (fuel value : Nat) (locals : List (MR_LocalName × MR_Type))
    (prog : MR_Program) (valid : value < modulus 64) :
    MRf.ArgumentExpr.check_wf (fuel + 21)
      (.ByValue (.Constant (.Int (Int.ofNat value)) (.Int (mrIntTy false .u64)))) locals prog =
        SOut.ok (.ok (.Int (mrIntTy false .u64))) := by
  simp only [MRf.ArgumentExpr.check_wf]
  rw [u64_expression fuel value locals prog valid]
  rfl

theorem result_place (fuel input : Nat) (prog : MR_Program) :
    MRf.PlaceExpr.check_wf (fuel + 2) (.Local ⟨1⟩) (entry input).locals prog =
      SOut.ok (.ok (.Int (mrIntTy false .u64))) := rfl

theorem result_storage (fuel input : Nat) (prog : MR_Program) :
    MRf.Statement.check_wf (fuel + 2) (.StorageLive ⟨1⟩) (entry input) prog =
      SOut.ok (.ok ()) := rfl

theorem next_block (fuel input : Nat) :
    MRf.Function.check_next_block (fuel + 2) (entry input) .Regular ⟨1⟩ =
      SOut.ok (.ok ()) := rfl

theorem return_block (fuel input : Nat) (prog : MR_Program) :
    MRf.Terminator.check_wf (fuel + 2) .Return .Regular (entry input) prog =
      SOut.ok (.ok ()) := rfl

theorem call_wellformed (fuel literal input : Nat) (inputValid : input < modulus 64) :
    MRf.Terminator.check_wf (fuel + 40) (callTerm input) .Regular
      (entry input) (program literal input) = SOut.ok (.ok ()) := by
  have ptrChecked (k : Nat) (locals : List (MR_LocalName × MR_Type)) :=
    pointer_expression k literal input locals
  have argChecked (k : Nat) (locals : List (MR_LocalName × MR_Type)) :=
    u64_argument k input locals (program literal input) inputValid
  have placeChecked (k : Nat) := result_place k input (program literal input)
  have nextChecked (k : Nat) := next_block k input
  unfold callTerm
  simp only [MRf.Terminator.check_wf, ptrChecked, argChecked, placeChecked, nextChecked,
    MiniRustU64Function.layout_u64, SBool.not, SLoop.forS, SOut.bind, MRf.fn.ensure_wf,
    MRf.LayoutStrategy.is_sized]

theorem entry_wellformed (fuel literal input : Nat) (inputValid : input < modulus 64) :
    MRf.Function.check_wf (fuel + 64) (entry input) (program literal input) =
      SOut.ok (.ok ()) := by
  have callChecked (k : Nat) := call_wellformed k literal input inputValid
  have storageChecked (k : Nat) := result_storage k input (program literal input)
  have returnChecked (k : Nat) := return_block k input (program literal input)
  have u64Checked (k : Nat) := u64_type k (program literal input)
  have unitChecked (k : Nat) := unit_type k (program literal input)
  simp only [MRf.Function.check_wf, entry_locals, entry_args, entry_ret, entry_blocks,
    callBlock, returnBlock, callChecked, storageChecked, returnChecked,
    u64Checked, unitChecked, MiniRustU64Function.layout_u64, MiniRustU64Program.unit_layout, SBool.not,
    SList.appendL, SList.push, SLoop.forS, SMap.contains_key, SMap.get,
    SMap.getL, SMap.values, SOption.is_some, SOut.bind, SRes.is_err,
    SSet.contains, SSet.try_insert, MR_LocalName.beq, MRf.fn.ensure_wf, MRf.LayoutStrategy.is_sized]

theorem value_callback (fuel : Nat) (value : MR_ValueExpr)
    (locals : List (MR_LocalName × MR_Type)) (prog : MR_Program) :
    (MR_rec_38.tie fuel).f_MRf_ValueExpr_check_wf fuel value locals prog =
      MRf.ValueExpr.check_wf fuel value locals prog := rfl

theorem scalar_load (fuel literal : Nat) (prog : MR_Program) :
    MRf.ValueExpr.check_wf (fuel + 20) (.Load (.Local ⟨1⟩)) (function literal).locals prog =
      SOut.ok (.ok (.Int (mrIntTy false .u64))) := rfl

theorem scalar_result (fuel literal : Nat) (prog : MR_Program) :
    MRf.PlaceExpr.check_wf (fuel + 2) (.Local ⟨0⟩) (function literal).locals prog =
      SOut.ok (.ok (.Int (mrIntTy false .u64))) := rfl

theorem scalar_add (fuel literal : Nat) (prog : MR_Program)
    (literalValid : literal < modulus 64) :
    MRf.ValueExpr.check_wf (fuel + 40)
      (.BinOp (.Int .Add) (.Load (.Local ⟨1⟩))
        (.Constant (.Int (Int.ofNat literal)) (.Int (mrIntTy false .u64))))
      (function literal).locals prog = SOut.ok (.ok (.Int (mrIntTy false .u64))) := by
  have literalChecked (k : Nat) := u64_expression k literal (function literal).locals prog literalValid
  have loadChecked (k : Nat) := scalar_load k literal prog
  change MRf.ValueExpr.check_wf_open (MR_rec_38.tie (fuel + 39)) (fuel + 40)
    (.BinOp (.Int .Add) (.Load (.Local ⟨1⟩))
      (.Constant (.Int (Int.ofNat literal)) (.Int (mrIntTy false .u64))))
    (function literal).locals prog = SOut.ok (.ok (.Int (mrIntTy false .u64)))
  simp only [MRf.ValueExpr.check_wf_open, value_callback, literalChecked, loadChecked, SOut.bind_ok']
  rfl

theorem scalar_assign (fuel literal : Nat) (prog : MR_Program)
    (literalValid : literal < modulus 64) :
    MRf.Statement.check_wf (fuel + 48)
      (.Assign (.Local ⟨0⟩) (.BinOp (.Int .Add) (.Load (.Local ⟨1⟩))
        (.Constant (.Int (Int.ofNat literal)) (.Int (mrIntTy false .u64)))))
      (function literal) prog = SOut.ok (.ok ()) := by
  have addChecked (k : Nat) := scalar_add k literal prog literalValid
  have placeChecked (k : Nat) := scalar_result k literal prog
  simp only [MRf.Statement.check_wf, addChecked, placeChecked, SOut.bind_ok']
  rfl

theorem scalar_return (fuel literal : Nat) (prog : MR_Program) :
    MRf.Terminator.check_wf (fuel + 2) .Return .Regular (function literal) prog =
      SOut.ok (.ok ()) := rfl

theorem scalar_blocks (literal : Nat) :
    (function literal).blocks = [(⟨0⟩,
      { statements := [.Assign (.Local ⟨0⟩) (.BinOp (.Int .Add) (.Load (.Local ⟨1⟩))
          (.Constant (.Int (Int.ofNat literal)) (.Int (mrIntTy false .u64))))]
        terminator := .Return, kind := .Regular })] := rfl

theorem scalar_wellformed (fuel literal : Nat) (prog : MR_Program)
    (literalValid : literal < modulus 64) :
    MRf.Function.check_wf (fuel + 64) (function literal) prog = SOut.ok (.ok ()) := by
  have assignChecked (k : Nat) := scalar_assign k literal prog literalValid
  have returnChecked (k : Nat) := scalar_return k literal prog
  have typeChecked (k : Nat) := u64_type k prog
  simp only [MRf.Function.check_wf, MiniRustU64Call.function_return, MiniRustU64Call.function_arguments, MiniRustU64Call.function_local_types, scalar_blocks,
    assignChecked, returnChecked, typeChecked, MiniRustU64Function.layout_u64, SBool.not,
    SList.appendL, SList.push, SLoop.forS, SMap.contains_key, SMap.get,
    SMap.getL, SMap.values, SOption.is_some, SOut.bind, SRes.is_err,
    SSet.contains, SSet.try_insert, MR_LocalName.beq, MRf.fn.ensure_wf, MRf.LayoutStrategy.is_sized]

theorem program_functions (literal input : Nat) :
    (program literal input).functions = [(⟨0⟩, entry input), (⟨1⟩, function literal)] := rfl
theorem program_start (literal input : Nat) : (program literal input).start = ⟨0⟩ := rfl
theorem program_globals (literal input : Nat) : (program literal input).globals = [] := rfl
theorem program_traits (literal input : Nat) : (program literal input).traits = [] := rfl
theorem program_vtables (literal input : Nat) : (program literal input).vtables = [] := rfl
theorem entry_convention (input : Nat) : (entry input).calling_convention = .C := rfl

theorem unit_layout_equal (fuel : Nat) :
    MR_LayoutStrategy.beq (fuel + 2) (.Sized 0 1) (.Sized 0 1) = SOut.ok true := rfl

/-- Every full64 literal/input pair is checked by the unchanged generated
    whole-program validator, including both real functions and the C/unit
    startup signature. There is no successful startup or function-check premise. -/
theorem program_wellformed (fuel literal input : Nat)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    MRf.Program.check_wf (fuel + 80) (program literal input) = SOut.ok (.ok ()) := by
  have entryChecked (k : Nat) := entry_wellformed k literal input inputValid
  have scalarChecked (k : Nat) := scalar_wellformed k literal (program literal input) literalValid
  simp only [MRf.Program.check_wf, program_functions, program_start, program_globals, program_traits,
    program_vtables, entry_convention, entry_locals, entry_ret, entry_args,
    entryChecked, scalarChecked, MiniRustU64Program.unit_layout, unit_layout_equal, MR_CallingConvention.beq,
    MR_FnName.beq, SBool.not, SList.len, SLoop.forS, SMap.get,
    SMap.getL, SMap.index_at, SMap.values, SOption.unwrap, SOut.bind,
    MR_LocalName.beq, MRf.fn.ensure_wf, SInt.beq]

  rfl

#print axioms program_wellformed

end MiniRustU64ProgramTyping
