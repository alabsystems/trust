/- Operational prerequisite for proposed canonical evaluator DATA. The proposed
   Module is the decoder author's unchanged packet02 quotation. Its exact-wire
   equation is a separate pending obligation; no accepted-source, physical
   closure, runtime, ABI, object or admission claim is supplied here. -/
import ActualClosureModuleData
import ClosureU64Caller
import TrustIr.DecodedContext
import TrustIr.Proofs.SSACharProps

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

set_option maxRecDepth 2048

theorem context_succeeds (depth : Nat) :
    (contextOf ActualClosureModuleData.proposedModule (depth + 3)).toOption.isSome = true := by
  rfl

/-- Extract only after proving the actual complete context constructor succeeds.
    There is no default context or assumed returning evaluator run. -/
noncomputable def context (depth : Nat) : EvalContext :=
  (contextOf ActualClosureModuleData.proposedModule (depth + 3)).toOption.get
    (context_succeeds depth)

theorem context_exact (depth : Nat) :
    contextOf ActualClosureModuleData.proposedModule (depth + 3) = .ok (context depth) := by
  rfl

noncomputable def caller : EvalFunction := ((context 0).functions callerId).get (by rfl)
noncomputable def maker : EvalFunction := ((context 0).functions makerId).get (by rfl)
noncomputable def application : EvalFunction := ((context 0).functions applyId).get (by rfl)
noncomputable def target : EvalFunction := ((context 0).functions targetId).get (by rfl)

noncomputable def callerContext (depth : Nat) := (context depth).forFunction caller
noncomputable def makerContext (depth : Nat) := (context depth).forFunction maker
noncomputable def applicationContext (depth : Nat) := (context depth).forFunction application
noncomputable def targetContext (depth : Nat) := (context depth).forFunction target

theorem caller_lookup (depth : Nat) : (context depth).functions callerId = some caller := by rfl
theorem maker_lookup (depth : Nat) : (context depth).functions makerId = some maker := by rfl
theorem application_lookup (depth : Nat) : (context depth).functions applyId = some application := by rfl
theorem target_lookup (depth : Nat) : (context depth).functions targetId = some target := by rfl

theorem owned_roster : ActualClosureModuleData.proposedModule.functions.map (·.id) =
    [callerId, makerId, applyId, targetId] := rfl

theorem original_and_lifted_names :
    ActualClosureModuleData.proposedModule.functions.map (·.name) =
      ["EscapingOriginal.useAffine", "EscapingOriginal.makeAffine", "EscapingOriginal.apply64",
       "EscapingOriginal.makeAffine.__typed_closure_target"] := rfl

theorem complete_type_rows : ActualClosureModuleData.proposedModule.funcTys.length = 5 := rfl

theorem original_order (depth : Nat) : (context depth).functionOrder =
    some [callerId, makerId, applyId, targetId] := rfl

theorem no_body_errors (depth : Nat) :
    (context depth).functionErrors callerId = none ∧
    (context depth).functionErrors makerId = none ∧
    (context depth).functionErrors applyId = none ∧
    (context depth).functionErrors targetId = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem canonical_function_headers (depth : Nat) :
    (context depth).functionHeaders callerId = some (.ok { signature :=
      { params := [.U64, .U64, .U64], returns := [.U64], isVararg := false }, callingConv := .Rust }) ∧
    (context depth).functionHeaders makerId = some (.ok { signature :=
      { params := [.U64, .U64], returns := [.Closure nominal], isVararg := false }, callingConv := .Rust }) ∧
    (context depth).functionHeaders applyId = some (.ok { signature :=
      { params := [.Closure nominal, .U64], returns := [.U64], isVararg := false }, callingConv := .Rust }) ∧
    (context depth).functionHeaders targetId = some (.ok { signature :=
      { params := [.U64, .U64, .U64], returns := [.U64], isVararg := false }, callingConv := .Rust }) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem inferred_locals_present : caller.localTypes.isSome = true ∧
    maker.localTypes.isSome = true ∧ application.localTypes.isSome = true ∧
    target.localTypes.isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memory_service_present (depth : Nat) : (context depth).memoryService.isSome = true := rfl

theorem caller_block : caller.cfg ⟨0⟩ = some ClosureU64.callerBlock := rfl
theorem maker_block : maker.cfg ⟨0⟩ = some ClosureU64.makerBlock := rfl
theorem application_block : application.cfg ⟨0⟩ = some ClosureU64.applicationBlock := rfl
theorem target_block : target.cfg ⟨0⟩ = some ClosureU64.targetBlock := rfl

theorem for_maker (depth : Nat) : (callerContext depth).forFunction maker = makerContext depth := rfl
theorem for_application (depth : Nat) :
    (callerContext depth).forFunction application = applicationContext depth := rfl
theorem for_target (depth : Nat) :
    (applicationContext depth).forFunction target = targetContext depth := rfl

theorem target_contract (ctx : EvalContext)
    (found : ctx.functions targetId = some target)
    (apparentFound : ctx.funcTys apparent =
      some { params := [.U64], returns := [.U64], isVararg := false })
    (closureFound : ctx.closures nominal =
      some { func := apparent, captures := [.U64, .U64] }) :
    closureContract ctx nominal targetId = .ok
      ({ func := apparent, captures := [.U64, .U64] },
       { params := [.U64], returns := [.U64], isVararg := false }, target) := by
  simp only [closureContract, closureFound, bind, pure, Except.bind, Except.pure,
    apparentFound, found]
  rfl

#print axioms context_exact
#print axioms canonical_function_headers
#print axioms inferred_locals_present
end CanonicalClosure
