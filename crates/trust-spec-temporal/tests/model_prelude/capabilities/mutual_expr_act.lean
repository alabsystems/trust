-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- mutual Expr/Act nested through List, Option and Prod; required pass.

namespace Trust
namespace Model

mutual
inductive Expr where
  | lit     : Nat → Expr
  | cur     : Nat → Expr
  | op      : Nat → List Expr → Expr
  | ite     : Expr → Expr → Expr → Expr
  | caseOf  : List (Expr × Expr) → Option Expr → Expr
  | enabled : Act → Expr
inductive Act where
  | conj    : List Act → Act
  | pred    : Expr → Act
  | prime   : Nat → Expr → Act
  | caseOf  : List (Expr × Act) → Option Act → Act
end

def a1 : Act :=
  Act.conj [Act.prime 0 (Expr.lit 1),
    Act.pred (Expr.enabled (Act.caseOf [(Expr.cur 0, Act.conj [])] (some (Act.conj []))))]

-- One-type dispatch through the block's casesOn (B1A-D70). It takes one motive per type
-- of the block plus one per distinct nested instantiation, in the order Clean discovers
-- them: Expr, Act, List Expr, List (Expr × Expr), Option Expr, List Act,
-- List (Expr × Act), Option Act, Expr × Expr, Expr × Act (ten; measured by B1A-02b,
-- model_prelude_kernel::clean_capabilities_doors also asserts Expr.rec's count). Then
-- the major premise, then a minor for every constructor of every one of those types.
def Expr.tag (e : Expr) : Nat :=
  @Expr.casesOn (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) e
    (fun _ => 0) (fun _ => 1) (fun _ _ => 2) (fun _ _ _ => 3) (fun _ _ => 4) (fun _ => 5)
    (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ _ => 0)
    0 (fun _ => 0)
    (fun _ _ => 0)
    (fun _ _ => 0)

-- One-type dispatch on a mutual inductive through `match` (one motive).
def Act.width (a : Act) : Nat :=
  match a with
  | .conj as => as.length
  | _ => 0

def Expr.isEnabled (e : Expr) : Bool :=
  match e with
  | .enabled _ => true
  | _ => false

theorem mutual_expr_act_door : Nat.beq (Act.width a1) 2 = true := rfl
theorem mutual_expr_act_expr : Expr.isEnabled (Expr.enabled (Act.conj [])) = true := rfl
theorem mutual_expr_act_casesOn_door :
    Nat.beq (Expr.tag (Expr.caseOf [] (some (Expr.lit 0)))) 4 = true := rfl

end Model
end Trust
