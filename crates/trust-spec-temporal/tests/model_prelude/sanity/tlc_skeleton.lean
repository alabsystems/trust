-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-14a sanity facts for Trust.Model.Tlc's skeleton (model_prelude_kernel.rs,
-- sanity_files): each of the nine design functions typed against its signature in design
-- 10:285-298 (the `sig*` definitions, which elaborate only at exactly that type) and run
-- through the block (B1A-D07): fuel 0 is `Fail.fuel` (10:98), and at fuel 1 every case of
-- the skeleton answers `unmodeled todo` (the rows that fill a case change its fact here:
-- B1A-14b changed `block_evalX` and `block_force`; B1A-16 `block_force`, `block_applyX`
-- and `block_memX`);
-- an answer of another result type is `Fail.fuel` (B1A-D92); the six forcing rules give
-- TLC's behaviour only (B1A-D36: the forcing callbacks are never called, shown by passing
-- callbacks that raise); and the well-formedness deciders (10:250-256) on controls.
-- Elaborated after the whole model prelude; every theorem is accepted by
-- check_model_theorem and is a Bool door closed by rfl (B1A-D54); the mutated-literal doors
-- of SANITY_MUTANTS must each be refuted (class Definite).
--
-- The expectations are the design's rules applied by hand: Reducible is a `val` finite set
-- (10:590), keepLazy resets at an item's right-hand side (10:591), assignments and
-- constructor domains stay unforced (10:614, 10:620), filters are eager exactly over a
-- Reducible base (10:628), lazy membership is pointwise (10:622).

namespace Trust
namespace Model
namespace Sanity

def int (n : Int) : Value := Value.int n

-- A one-variable spec with nothing in it.
def sp1 : Spec :=
  Spec.mk 1 IntMode.tlc32 [] [] [] [] [] (Act.conj []) (Act.conj []) [] [] [] [] true
    ChoiceMode.none

-- ---- The nine functions at their design types (10:285-298) ----

def sigEvalX : Spec → Nat → Bool → List Value → State → Frame → Expr → Res XVal := evalX
def sigForce : Spec → Nat → State → XVal → Res Value := force
def sigApplyX : Spec → Nat → Bool → State → XVal → Value → Res XVal := applyX
def sigMemX : Spec → Nat → State → XVal → Value → Res Bool := memX
def sigEnumNext : Spec → Nat → State → SetGen → Nat → Res (Option (Value × Nat)) := enumNext
def sigEnumAll : Spec → Nat → State → SetGen → Res (List Value) := enumAll
def sigTlcEnumF : Spec → Nat → List Value → Act → State → Res (List State) := tlcEnumF
def sigTlcEnabledF : Spec → Nat → List Value → Act → State → Res Bool := tlcEnabledF
def sigTlcHoldsF : Spec → Nat → List Value → Act → State → State → Res Bool := tlcHoldsF

-- ---- Reading results ----

def isFuel {α : Type} (r : Res α) : Bool :=
  @Res.rec α (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun _ => false) false false true (fun _ => false))
    r

def isUnmodeled {α : Type} (r : Res α) (code : Nat) : Bool :=
  @Res.rec α (fun _ => Bool) (fun _ => false)
    (fun f => @Fail.casesOn (fun _ => Bool) f false false false false false false false false
      false (fun _ => false) false false false (fun c => Nat.beq c code))
    r

def isOkWith {α : Type} (r : Res α) (p : α → Bool) : Bool :=
  @Res.rec α (fun _ => Bool) (fun a => p a) (fun _ => false) r

-- The constructor of an XVal: 0 val, 1 lazyFn, 2 fnX, 3 lazySet.
def xTag (x : XVal) : Nat := XVal.elim x (fun _ => 0) (fun _ _ _ => 1) (fun _ => 2) (fun _ => 3)

-- `fuel0And1 r0 r1`: r0 (fuel 0) is `Fail.fuel` and r1 (fuel 1) is the skeleton's todo.
def fuel0And1 {α : Type} (r0 r1 : Res α) : Bool :=
  Bool.and (isFuel r0) (isUnmodeled r1 Code.todo)

def tt : Expr := Expr.lit (Value.bool true)
def set12 : Value := Value.set [int 1, int 2]
def gSet : SetGen := SetGen.ofVal set12
def ctx0 : Ctx := Ctx.mk [] [Option.none]

-- ---- The block (B1A-D07) ----

-- evalX and force: B1A-14b filled the cases these read (a literal; a forced `val`), so at
-- fuel 1 they answer the value (tlc_core.lean has the core cases); fuel 0 is still
-- `Fail.fuel`; an `op` (filled by B1A-15) evaluates its operands one level down, so at fuel 1
-- an op over literals is `Fail.fuel` and at fuel 2 its value; forcing a lazy set other than
-- an `ofVal` generator is still todo (B1A-17b; B1A-16 forces `ofVal` to its value).
theorem block_evalX :
    Bool.and (isFuel (sigEvalX sp1 0 false [] [int 0] [Option.none] tt))
    (Bool.and (isOkWith (sigEvalX sp1 1 false [] [int 0] [Option.none] tt)
      (fun x => Nat.beq (xTag x) 0))
    (Bool.and (isFuel (sigEvalX sp1 1 false [] [int 0] [Option.none] (Expr.op PrimOp.valueEq [tt, tt])))
      (isOkWith (sigEvalX sp1 2 false [] [int 0] [Option.none] (Expr.op PrimOp.valueEq [tt, tt]))
        (fun x => Nat.beq (xTag x) 0)))) = true := rfl
theorem block_force :
    Bool.and (isFuel (sigForce sp1 0 [int 0] (XVal.val set12)))
    (Bool.and (isOkWith (sigForce sp1 1 [int 0] (XVal.val set12)) (fun v => Value.beq v set12))
      (isUnmodeled (sigForce sp1 1 [int 0] (XVal.lazySet (SetGen.subset gSet))) Code.todo))
      = true := rfl
-- applyX (B1A-16): a `val` function applied at fuel 1 is its value (sanity lazy_fn.lean has
-- the lazy cases); memX (B1A-16's part: a forced set or `ofVal`) of a lazy SUBSET is still
-- todo (B1A-17a).
theorem block_applyX :
    Bool.and (isFuel (sigApplyX sp1 0 true [int 0] (XVal.val (Value.fn [(int 1, int 5)])) (int 1)))
      (isOkWith (sigApplyX sp1 1 true [int 0] (XVal.val (Value.fn [(int 1, int 5)])) (int 1))
        (fun x => Nat.beq (xTag x) 0)) = true := rfl
theorem block_memX : fuel0And1 (sigMemX sp1 0 [int 0] (XVal.lazySet (SetGen.subset gSet)) (int 1))
    (sigMemX sp1 1 [int 0] (XVal.lazySet (SetGen.subset gSet)) (int 1)) = true := rfl
theorem block_enumNext : fuel0And1 (sigEnumNext sp1 0 [int 0] gSet 0)
    (sigEnumNext sp1 1 [int 0] gSet 0) = true := rfl
theorem block_enumAll : fuel0And1 (sigEnumAll sp1 0 [int 0] gSet)
    (sigEnumAll sp1 1 [int 0] gSet) = true := rfl
theorem block_tlcEnumF : fuel0And1 (sigTlcEnumF sp1 0 [] (Act.prime 0 tt) [int 0])
    (sigTlcEnumF sp1 1 [] (Act.prime 0 tt) [int 0]) = true := rfl
theorem block_tlcEnabledF : fuel0And1 (sigTlcEnabledF sp1 0 [] (Act.prime 0 tt) [int 0])
    (sigTlcEnabledF sp1 1 [] (Act.prime 0 tt) [int 0]) = true := rfl
theorem block_tlcHoldsF : fuel0And1 (sigTlcHoldsF sp1 0 [] (Act.prime 0 tt) [int 0] [int 1])
    (sigTlcHoldsF sp1 1 [] (Act.prime 0 tt) [int 0] [int 1]) = true := rfl

-- An answer of another result type is `Fail.fuel` (B1A-D92), never a TLC error.
theorem block_mismatch_is_fuel :
    Bool.and (isFuel (Tlc.goEvalX (fun _ => Res.ok (Out.bool true)) false [] [] [] tt))
      (isFuel (Tlc.goMemX (fun _ => Res.ok (Out.value (int 1))) [] (XVal.val set12) (int 1)))
      = true := rfl

-- The job's own answer passes through its projection.
theorem block_projection_passes :
    isOkWith (Tlc.goForce (fun _ => Res.ok (Out.value (int 7))) [] (XVal.val set12))
      (fun v => Value.beq v (int 7)) = true := rfl

-- ---- The forcing rules: TLC's behaviour only (B1A-D36) ----

-- A callback that raises: a rule that called it would answer its error.
def raise (_x : XVal) : Res Value := Res.error Fail.divZero
def raiseMem (_a _b : Value) : Res Bool := Res.error Fail.divZero

-- Row 1: materialized iff keepLazy is off and every domain is a `val` finite set.
theorem rule_materializeQFn :
    Bool.and (Tlc.rule.materializeQFn false [XVal.val set12, XVal.val (Value.set [])])
    (Bool.and (Bool.not (Tlc.rule.materializeQFn true [XVal.val set12]))
    (Bool.and (Bool.not (Tlc.rule.materializeQFn false [XVal.val set12, XVal.lazySet gSet]))
    (Bool.and (Bool.not (Tlc.rule.materializeQFn false [XVal.val (Value.infSet InfKind.nat [])]))
      (Tlc.rule.materializeQFn false [])))) = true := rfl

-- Row 1: constructor domains kept as evaluated, never forced.
theorem rule_forceCtorDomains :
    isOkWith (Tlc.rule.forceCtorDomains raise [XVal.lazySet gSet, XVal.val set12])
      (fun ds => Bool.and (Nat.beq (List.length ds) 2)
        (Nat.beq (xTag (Temporal.nthD ds 0 (XVal.val set12))) 3)) = true := rfl

-- Row 2: an item's right-hand side runs under Clear whatever the control was.
theorem rule_keepLazyReset :
    Bool.and (Bool.not (Tlc.rule.keepLazyReset true)) (Bool.not (Tlc.rule.keepLazyReset false))
      = true := rfl

-- Generate mode: an assignment binds its value unforced.
theorem rule_forceAtAssign :
    isOkWith (Tlc.rule.forceAtAssign raise (XVal.lazySet gSet)) (fun x => Nat.beq (xTag x) 3)
      = true := rfl

-- 10:628: eager exactly over a Reducible base.
theorem rule_eagerFilter :
    Bool.and (Tlc.rule.eagerFilter (XVal.val set12))
    (Bool.and (Bool.not (Tlc.rule.eagerFilter (XVal.val (Value.infSet InfKind.int []))))
      (Bool.not (Tlc.rule.eagerFilter (XVal.lazySet (SetGen.subset gSet))))) = true := rfl

-- 10:622: pointwise, never by forcing.
theorem rule_memByForcing :
    Bool.and (isOkWith (Tlc.rule.memByForcing raise raiseMem (Res.ok true)
        (XVal.lazySet (SetGen.subset gSet)) set12) (fun b => b))
      (isOkWith (Tlc.rule.memByForcing raise raiseMem (Res.ok false)
        (XVal.lazySet (SetGen.subset gSet)) set12) (fun b => Bool.not b)) = true := rfl

-- ---- Well-formedness (10:250-256) ----

-- A one-binder closure body reading its argument, at one bound value.
def body0 : Expr := Expr.bvar 0
def ctxOk : Ctx := Ctx.mk [int 3] [Option.some (XVal.val (int 5))]

theorem wf_val : Bool.and (XVal.wfB sp1 (XVal.val set12))
    (Bool.not (XVal.wfB sp1 (XVal.val (Value.set [int 2, int 1])))) = true := rfl

theorem wf_fnX :
    Bool.and (XVal.wfB sp1 (XVal.fnX [(int 1, XVal.lazySet gSet), (int 2, XVal.val set12)]))
    (Bool.and (Bool.not (XVal.wfB sp1 (XVal.fnX [(int 2, XVal.val set12), (int 1, XVal.val set12)])))
      (Bool.not (XVal.wfB sp1 (XVal.fnX [(int 1, XVal.val (Value.set [int 2, int 1]))])))) = true := rfl

theorem wf_lazyFn :
    Bool.and (XVal.wfB sp1 (XVal.lazyFn [gSet] (Expr.bvar 1) ctxOk))
    (Bool.and (Bool.not (XVal.wfB sp1 (XVal.lazyFn [gSet] (Expr.bvar 2) ctxOk)))
    (Bool.and (Bool.not (XVal.wfB sp1 (XVal.lazyFn [gSet] body0 (Ctx.mk [] []))))
      (Bool.not (XVal.wfB sp1 (XVal.lazyFn [SetGen.ofVal (Value.set [int 2, int 1])] body0 ctx0)))))
      = true := rfl

theorem wf_setGen :
    Bool.and (SetGen.wfB sp1 (SetGen.filter (SetGen.subset gSet) body0 ctx0))
    (Bool.and (Bool.not (SetGen.wfB sp1 (SetGen.filter gSet (Expr.bvar 1) ctx0)))
    (Bool.and (SetGen.wfB sp1 (SetGen.rcdSet [(4, gSet), (5, SetGen.fnSet gSet gSet)]))
      (Bool.not (SetGen.wfB sp1 (SetGen.prod [gSet, SetGen.ofVal (Value.set [int 2, int 1])])))))
      = true := rfl

theorem wf_ctx :
    Bool.and (Ctx.wfB sp1 ctxOk)
    (Bool.and (Bool.not (Ctx.wfB sp1 (Ctx.mk [int 3] [])))
    (Bool.and (Bool.not (Ctx.wfB sp1 (Ctx.mk [Value.set [int 2, int 1]] [Option.none])))
      (Bool.not (Ctx.wfB sp1 (Ctx.mk [] [Option.some (XVal.val (Value.set [int 2, int 1]))])))))
      = true := rfl

-- The block's recursor order (B1A-D70), measured: each of the ten motives gets its own
-- type, so `XVal.rec` elaborates only in Clean's discovery order: Ctx, SetGen, XVal,
-- List (Option XVal), List SetGen, List (Nat × SetGen), List (Value × XVal), Option XVal,
-- Nat × SetGen, Value × XVal.
def motiveOrder (x : XVal) : Nat :=
  @XVal.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Bool) (fun _ => Int) (fun _ => List Nat) (fun _ => List Bool)
    (fun _ => Option Nat) (fun _ => Option Bool) (fun _ => Option Int)
    (fun _ _ _ => 0)
    (fun _ => 0) (fun _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ _ _ => 0)
    (fun _ => 1) (fun _ _ _ _ _ => 2) (fun _ _ => 3) (fun _ _ => 4)
    true (fun _ _ _ _ => true)
    (0 : Int) (fun _ _ _ _ => (0 : Int))
    ([] : List Nat) (fun _ _ _ _ => ([] : List Nat))
    ([] : List Bool) (fun _ _ _ _ => ([] : List Bool))
    (Option.none : Option Nat) (fun _ _ => (Option.none : Option Nat))
    (fun _ _ _ => (Option.none : Option Bool))
    (fun _ _ _ => (Option.none : Option Int))
    x
theorem motive_order :
    Bool.and (Nat.beq (motiveOrder (XVal.fnX [])) 3) (Nat.beq (motiveOrder (XVal.lazySet gSet)) 4)
      = true := rfl

-- The projections of the single-constructor Ctx (B1A-D21).
theorem ctx_projections :
    Bool.and (Nat.beq (List.length (Ctx.env ctxOk)) 1) (Nat.beq (List.length (Ctx.post ctxOk)) 1)
      = true := rfl

end Sanity
end Model
end Trust
