-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02b Clean capability matrix II (model_prelude_kernel.rs, clean_capabilities_doors):
-- audit_certification (clean_surface.rs checked_theorem) on theorems whose dependency
-- closure reaches a nested inductive's auxiliary recursors, a mutual block's
-- recursors, a structure's projections, a Nat.rec fuel definition and a
-- match-compiled definition. The test also asserts each of those constants is in the
-- audited closure, so the audit is not passed vacuously.

namespace Trust
namespace Model

-- A nested inductive (design 10:71-107 shape): Value through List and Prod.
inductive Value where
  | int : Int → Value
  | set : List Value → Value
  | fn  : List (Value × Value) → Value

-- The block's recursor, every motive: Value, List Value, List (Value × Value),
-- Value × Value; then the minors of each, with induction hypotheses.
def Value.count (v : Value) : Nat :=
  @Value.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => 1) (fun _ ih => ih + 1) (fun _ ih => ih + 1)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    (fun _ _ ih1 ih2 => ih1 + ih2)
    v

-- The nested auxiliary recursor for List Value, named directly.
def Value.countList (vs : List Value) : Nat :=
  @Value.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => 1) (fun _ ih => ih + 1) (fun _ ih => ih + 1)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    (fun _ _ ih1 ih2 => ih1 + ih2)
    vs

def v1 : Value := Value.set [Value.int 3, Value.fn [(Value.int 1, Value.int 2)]]

-- The nested auxiliary recursor for List (Value × Value), named directly.
def Value.countPairs (ps : List (Value × Value)) : Nat :=
  @Value.rec_2 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => 1) (fun _ ih => ih + 1) (fun _ ih => ih + 1)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    0 (fun _ _ ih1 ih2 => ih1 + ih2)
    (fun _ _ ih1 ih2 => ih1 + ih2)
    ps

theorem audit_nested : Nat.beq (Value.count v1) 5 = true := rfl
theorem audit_nested_aux : Nat.beq (Value.countList [v1, Value.int 0]) 6 = true := rfl
theorem audit_nested_aux_pairs :
    Nat.beq (Value.countPairs [(v1, Value.int 0), (Value.int 1, Value.int 2)]) 8 = true := rfl

-- A mutual block, both recursors.
mutual
inductive Expr where
  | lit : Nat → Expr
  | enabled : Act → Expr
inductive Act where
  | pred : Expr → Act
  | conj : Act → Act → Act
end

def Expr.depth (e : Expr) : Nat :=
  @Expr.rec (fun _ => Nat) (fun _ => Nat)
    (fun _ => 0) (fun _ ih => ih + 1)
    (fun _ ih => ih + 1) (fun _ _ ih1 ih2 => Nat.max ih1 ih2 + 1)
    e

def Act.depth (a : Act) : Nat :=
  @Act.rec (fun _ => Nat) (fun _ => Nat)
    (fun _ => 0) (fun _ ih => ih + 1)
    (fun _ ih => ih + 1) (fun _ _ ih1 ih2 => Nat.max ih1 ih2 + 1)
    a

theorem audit_mutual : Nat.beq (Expr.depth (Expr.enabled (Act.pred (Expr.lit 0)))) 2 = true := rfl
theorem audit_mutual_act :
    Nat.beq (Act.depth (Act.conj (Act.pred (Expr.lit 0)) (Act.pred (Expr.lit 1)))) 2 = true := rfl

-- A structure's projections (Spec, design 10:180-205, cut down).
structure Spec where
  vars : Nat
  init : List Nat
  next : Nat

def sp1 : Spec := { vars := 2, init := [1, 2, 3], next := 7 }

-- Field notation elaborates to the kernel's projection node (`Proj` on Spec); naming the
-- projection function applies the projection definition.
theorem audit_projection : Nat.beq (sp1.vars + sp1.init.length + sp1.next) 12 = true := rfl
theorem audit_projection_fn : Nat.beq (Spec.next sp1) 7 = true := rfl

-- A Nat.rec fuel definition (the B1A-D07 block's shape).
def runFuel (n : Nat) : Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun k => k) (fun _ go k => go (k + 2)) n

theorem audit_fuel : Nat.beq (runFuel 50 1) 101 = true := rfl

-- A match-compiled definition (its auxiliary is what B1A-D61 forbids in vocabulary).
def Value.isSet (v : Value) : Bool :=
  match v with
  | .set _ => true
  | _ => false

theorem audit_match : Value.isSet v1 = true := rfl

end Model
end Trust
