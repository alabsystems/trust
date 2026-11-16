/- Logical closure-conversion prerequisite over the unchanged pinned contextual
   evaluator. A typedClosure is a logical value, not a physical environment,
   boxed-runtime allocation, native ABI, canonical SemR byte interpretation or
   compiler permission. No carrier/admission or machine checker is changed. -/
import TrustIr.Proofs.ClosureProps
import ClosureSource
import Init.Data.UInt.Lemmas

namespace ClosureU64
open TrustIr
set_option maxRecDepth 8192

def nominal : ClosureTyId := ⟨0⟩
def apparent : FuncTyId := ⟨0⟩
def callerId : FuncId := ⟨0⟩
def makerId : FuncId := ⟨1⟩
def applyId : FuncId := ⟨2⟩
def targetId : FuncId := ⟨3⟩
def valueId (n : Nat) : ValueId := ⟨n⟩

def function (params returns : List Ty) (body : List Inst)
    (destinations : List (List ValueId)) (result : ValueId) : EvalFunction :=
  { body := { paramTys := params, returnTys := returns }
    cfg := fun pc => if pc == (⟨0⟩ : BlockId) then
      some {
        params := (params.zipIdx).map (fun (ty, index) => (valueId index, ty))
        body := body
        bodyResultDests := destinations
        terminator := .Return [result] } else none
    entryBlock := ⟨0⟩, callingConv := .Rust }

def target : EvalFunction := function [.U64, .U64, .U64] [.U64]
  [.BinOp .Mul .U64 (valueId 0) (valueId 2),
   .BinOp .Add .U64 (valueId 3) (valueId 1)]
  [[valueId 3], [valueId 4]] (valueId 4)

def maker : EvalFunction := function [.U64, .U64] [.Closure nominal]
  [.MakeClosure nominal targetId [valueId 0, valueId 1]]
  [[valueId 2]] (valueId 2)

def application : EvalFunction := function [.Closure nominal, .U64] [.U64]
  [.CallIndirect (valueId 0) apparent [valueId 1] .Rust]
  [[valueId 2]] (valueId 2)

def caller : EvalFunction := function [.U64, .U64, .U64] [.U64]
  [.Call makerId [valueId 0, valueId 1],
   .Call applyId [valueId 3, valueId 2]]
  [[valueId 3], [valueId 4]] (valueId 4)

def context (depth : Nat) : EvalContext :=
  { EvalContext.empty with
    maxCallDepth := depth + 3
    functions := fun id =>
      if id == callerId then some caller
      else if id == makerId then some maker
      else if id == applyId then some application
      else if id == targetId then some target else none
    funcTys := fun id => if id == apparent then
      some { params := [.U64], returns := [.U64], isVararg := false } else none
    closures := fun id => if id == nominal then
      some { func := apparent, captures := [.U64, .U64] } else none }

def word (value : UInt64) : Value := .int 64 (Int.ofNat value.toNat)

@[simp] theorem context_local_types (depth : Nat) : (context depth).localTypes = none := rfl

@[simp] theorem target_lookup (depth : Nat) : (context depth).functions targetId = some target := rfl

@[simp] theorem maker_lookup (depth : Nat) : (context depth).functions makerId = some maker := rfl

@[simp] theorem application_lookup (depth : Nat) :
    (context depth).functions applyId = some application := rfl

@[simp] theorem caller_lookup (depth : Nat) : (context depth).functions callerId = some caller := rfl

@[simp] theorem apparent_lookup (depth : Nat) :
    (context depth).funcTys apparent =
      some {params := [.U64], returns := [.U64], isVararg := false} := rfl

@[simp] theorem for_target (depth : Nat) : (context depth).forFunction target = context depth := rfl

@[simp] theorem for_maker (depth : Nat) : (context depth).forFunction maker = context depth := rfl

@[simp] theorem for_application (depth : Nat) :
    (context depth).forFunction application = context depth := rfl

@[simp] theorem for_caller (depth : Nat) : (context depth).forFunction caller = context depth := rfl

/-- Both environment fields remain ordered and the code identity is separate
    from them. It is not reconstructed from equal-width captures. -/
def closure (a b : UInt64) : Value :=
  .typedClosure nominal targetId [word a, word b]

theorem word_checked (ctx : EvalContext) (value : UInt64) :
    checkClosureValue ctx .U64 (word value) = .ok () := by
  have width : Ty.U64.bitWidthFor ctx.byteModel = some 64 := by
    cases ctx.byteModel <;> rfl
  have bound : (Int.ofNat value.toNat) < 18446744073709551616 :=
    Int.ofNat_lt.mpr value.toNat_lt_size
  simp only [Int.ofNat_eq_natCast] at bound
  simp [checkClosureValue, checkClosureValueAt, word,
    Value.isPoison, Value.isUninit, Ty.isInteger, width, bound,
    Except.bind, Except.pure, Bind.bind, Pure.pure] <;> rfl

theorem code_contract (depth : Nat) :
    closureContract (context depth) nominal targetId = .ok
      ({func := apparent, captures := [.U64, .U64]},
       {params := [.U64], returns := [.U64], isVararg := false}, target) := rfl

theorem pair_checked (ctx : EvalContext) (a b : UInt64) :
    ([Ty.U64, .U64].zip [word a, word b]).forM
      (fun (ty, value) => checkClosureValue ctx ty value) = .ok () := by
  change (do
    checkClosureValue ctx .U64 (word a)
    checkClosureValue ctx .U64 (word b)
    pure ()) = Except.ok ()
  rw [word_checked, word_checked]
  rfl

theorem argument_checked (ctx : EvalContext) (x : UInt64) :
    ([Ty.U64].zip [word x]).forM
      (fun (ty, value) => checkClosureValue ctx ty value) = .ok () := by
  change (do
    checkClosureValue ctx .U64 (word x)
    pure ()) = Except.ok ()
  rw [word_checked]
  rfl

theorem construction_exact (depth : Nat) (a b : UInt64) :
    makeClosureValue (context depth) nominal targetId [word a, word b] =
      .ok (closure a b) := by
  apply makeClosureValue_of_checked (d := {func := apparent, captures := [.U64, .U64]})
    (s := {params := [.U64], returns := [.U64], isVararg := false}) (f := target)
  · exact code_contract depth
  · rfl
  · exact pair_checked (context depth) a b

theorem application_arguments_exact (depth : Nat) (a b x : UInt64) :
    closureCall (context depth) nominal targetId [word a, word b]
      apparent [word x] .Rust = .ok (targetId, [word a, word b, word x]) := by
  apply closureCall_of_checked
    (d := {func := apparent, captures := [.U64, .U64]})
    (s := {params := [.U64], returns := [.U64], isVararg := false}) (f := target)
  · exact code_contract depth
  · rfl
  · rfl
  · exact construction_exact depth a b
  · rfl
  · exact argument_checked (context depth) x

#print axioms word_checked
#print axioms code_contract
#print axioms construction_exact
#print axioms application_arguments_exact
#print axioms TrustIr.evaluator_closure_preserves_pointer

end ClosureU64
