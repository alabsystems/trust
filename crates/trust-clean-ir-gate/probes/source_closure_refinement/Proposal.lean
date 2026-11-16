/- GENERATED UNTRUSTED PROPOSAL from Original's actual kernel definitions.
   This quotation supplies no source, runtime, ABI or object permission. -/
import Original
import ClosureU64
namespace SourceProposal
open TrustIr

def originalRoster : List (String × FuncId) :=
  [("EscapingOriginal.useAffine", ⟨0⟩), ("EscapingOriginal.makeAffine", ⟨1⟩), ("EscapingOriginal.apply64", ⟨2⟩)]
def liftedRoster : List (String × FuncId) := [("EscapingOriginal.makeAffine.__closure_target", ⟨3⟩)]

def target : EvalFunction := ClosureU64.function [.U64, .U64, .U64] [.U64]
  [.BinOp .Mul .U64 (ClosureU64.valueId 0) (ClosureU64.valueId 2),
   .BinOp .Add .U64 (ClosureU64.valueId 3) (ClosureU64.valueId 1)]
  [[(ClosureU64.valueId 3)], [(ClosureU64.valueId 4)]] (ClosureU64.valueId 4)

def maker : EvalFunction := ClosureU64.function [.U64, .U64] [.Closure ⟨0⟩]
  [.MakeClosure (⟨0⟩ : ClosureTyId) (⟨3⟩ : FuncId) [(ClosureU64.valueId 0), (ClosureU64.valueId 1)]]
  [[(ClosureU64.valueId 2)]] (ClosureU64.valueId 2)

def application : EvalFunction := ClosureU64.function [.Closure ⟨0⟩, .U64] [.U64]
  [.CallIndirect (ClosureU64.valueId 0) (⟨0⟩ : FuncTyId) [(ClosureU64.valueId 1)] .Rust]
  [[(ClosureU64.valueId 2)]] (ClosureU64.valueId 2)

def caller : EvalFunction := ClosureU64.function [.U64, .U64, .U64] [.U64]
  [.Call (⟨1⟩ : FuncId) [(ClosureU64.valueId 0), (ClosureU64.valueId 1)],
   .Call (⟨2⟩ : FuncId) [(ClosureU64.valueId 3), (ClosureU64.valueId 2)]]
  [[(ClosureU64.valueId 3)], [(ClosureU64.valueId 4)]] (ClosureU64.valueId 4)

def context (depth : Nat) : EvalContext :=
  { EvalContext.empty with
    maxCallDepth := depth + 3
    functions := fun id =>
      if id == (⟨0⟩ : FuncId) then some caller
      else if id == (⟨1⟩ : FuncId) then some maker
      else if id == (⟨2⟩ : FuncId) then some application
      else if id == (⟨3⟩ : FuncId) then some target else none
    funcTys := fun id => if id == (⟨0⟩ : FuncTyId) then
      some {params := [.U64], returns := [.U64], isVararg := false} else none
    closures := fun id => if id == (⟨0⟩ : ClosureTyId) then
      some {func := ⟨0⟩, captures := [.U64, .U64]} else none }

end SourceProposal
