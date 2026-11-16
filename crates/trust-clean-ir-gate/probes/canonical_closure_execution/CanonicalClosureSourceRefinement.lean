/- Generic source-equation refinement into the actual complete canonical
   context. Source functions are opaque arguments. Their exact captured CIC
   bindings and closed equation proofs must be supplied/rechecked separately;
   neither names nor DATA labels establish these premises. -/
import CanonicalClosureWords

namespace CanonicalClosure
open TrustIr TrustIrEval ClosureU64

structure SourceEquations
    (makeFn : UInt64 → UInt64 → UInt64 → UInt64)
    (applyFn : (UInt64 → UInt64) → UInt64 → UInt64)
    (callFn : UInt64 → UInt64 → UInt64 → UInt64) : Prop where
  make_eq : ∀ a b x, makeFn a b x = a * x + b
  apply_eq : ∀ f x, applyFn f x = f x
  call_eq : ∀ a b x, callFn a b x = applyFn (makeFn a b) x

/-- All four original/lifted roles use the unchanged full canonical context.
    The maker's logical code/captures represent makeFn through the target and
    application fields; this is no physical closure or foreign ABI relation. -/
structure SourceRefines
    (makeFn : UInt64 → UInt64 → UInt64 → UInt64)
    (applyFn : (UInt64 → UInt64) → UInt64 → UInt64)
    (callFn : UInt64 → UInt64 → UInt64 → UInt64) : Prop where
  equations : SourceEquations makeFn applyFn callFn
  maker : ∀ depth world a b,
    Sem.run (evalFunctionInContext (context depth) makerId [word a, word b] 1 .abort)
      (entryState world) = .ok ([closure a b], makerState world a b)
  target : ∀ depth world a b x,
    Sem.run (evalFunctionInContext (context depth) targetId [word a, word b, word x] 1 .abort)
      (entryState world) = .ok ([word (makeFn a b x)], targetState world a b x)
  application : ∀ depth world a b x,
    Sem.run (evalFunctionInContext (context depth) applyId [closure a b, word x] 2 .abort)
      (entryState world) = .ok ([word (applyFn (makeFn a b) x)], applicationState world a b x)
  caller : ∀ depth world a b x,
    Sem.run (evalFunctionInContext (context depth) callerId [word a, word b, word x] 3 .abort)
      (entryState world) = .ok ([word (callFn a b x)], callerState world a b x)
  raw_caller : ∀ depth world a b x,
    a < wordModulus → b < wordModulus → x < wordModulus →
    Sem.run (evalFunctionInContext (context depth) callerId [rawWord a, rawWord b, rawWord x] 3 .abort)
      (entryState world) =
      .ok ([rawWord ((a * x + b) % wordModulus)], rawCallerState world a b x)
  raw_source_result : ∀ a b x,
    (callFn (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat x)).toNat =
      (a * x + b) % wordModulus

/-- Pointwise premises are suitable for closed equation advice over the exact
    captured definitions. Every execution conclusion is constructed here; none
    is a returning-run premise. This does not qualify any concrete source by itself. -/
theorem source_refines_of_equations
    (makeFn : UInt64 → UInt64 → UInt64 → UInt64)
    (applyFn : (UInt64 → UInt64) → UInt64 → UInt64)
    (callFn : UInt64 → UInt64 → UInt64 → UInt64)
    (makeEq : ∀ a b x, makeFn a b x = a * x + b)
    (applyEq : ∀ f x, applyFn f x = f x)
    (callEq : ∀ a b x, callFn a b x = applyFn (makeFn a b) x) :
    SourceRefines makeFn applyFn callFn := by
  refine { equations := ⟨makeEq, applyEq, callEq⟩
           maker := ?_, target := ?_, application := ?_, caller := ?_
           raw_caller := ?_, raw_source_result := ?_ }
  · exact maker_evaluates
  · intro depth world a b x
    rw [makeEq]
    exact target_evaluates depth world a b x
  · intro depth world a b x
    rw [applyEq, makeEq]
    exact application_evaluates depth world a b x
  · intro depth world a b x
    rw [callEq, applyEq, makeEq]
    exact caller_evaluates depth world a b x
  · exact raw_caller_evaluates
  · intro a b x
    rw [callEq, applyEq, makeEq]
    exact affine_ofNat_toNat a b x

theorem SourceEquations.refines
    (makeFn : UInt64 → UInt64 → UInt64 → UInt64)
    (applyFn : (UInt64 → UInt64) → UInt64 → UInt64)
    (callFn : UInt64 → UInt64 → UInt64 → UInt64)
    (equations : SourceEquations makeFn applyFn callFn) : SourceRefines makeFn applyFn callFn :=
  source_refines_of_equations makeFn applyFn callFn equations.make_eq equations.apply_eq equations.call_eq

/-- A constructor from whole-function equalities, with no reflective source
    reader or semantic validator. The different verifier must check the actual
    closed premise terms and their exact original source/environment subjects. -/
theorem source_refines_of_closed_equalities
    (makeFn : UInt64 → UInt64 → UInt64 → UInt64)
    (applyFn : (UInt64 → UInt64) → UInt64 → UInt64)
    (callFn : UInt64 → UInt64 → UInt64 → UInt64)
    (makeEq : makeFn = fun a b x => a * x + b)
    (applyEq : applyFn = fun f x => f x)
    (callEq : callFn = fun a b x => applyFn (makeFn a b) x) :
    SourceRefines makeFn applyFn callFn :=
  source_refines_of_equations makeFn applyFn callFn
    (fun a b x => congrFun (congrFun (congrFun makeEq a) b) x)
    (fun f x => congrFun (congrFun applyEq f) x)
    (fun a b x => congrFun (congrFun (congrFun callEq a) b) x)

#print axioms source_refines_of_equations
#print axioms source_refines_of_closed_equalities
end CanonicalClosure
