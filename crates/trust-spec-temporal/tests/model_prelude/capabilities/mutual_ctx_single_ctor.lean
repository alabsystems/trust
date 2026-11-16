-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- Ctx as a single-constructor inductive in the mutual block, with projection defs (the B1A-D21 fallback); required pass.

namespace Trust
namespace Model

inductive Value where
  | int : Int → Value
  | set : List Value → Value

inductive Expr where
  | lit : Value → Expr
  | bvar : Nat → Expr

mutual
inductive Ctx where
  | mk : List Value → List (Option XVal) → Ctx
inductive SetGen where
  | ofVal  : Value → SetGen
  | subset : SetGen → SetGen
  | filter : SetGen → Expr → Ctx → SetGen
inductive XVal where
  | val     : Value → XVal
  | lazyFn  : List SetGen → Expr → Ctx → XVal
  | fnX     : List (Value × XVal) → XVal
  | lazySet : SetGen → XVal
end

-- B1A-D21 fallback: a single-constructor inductive with projection defs.
def Ctx.env (c : Ctx) : List Value :=
  match c with
  | .mk env _ => env

def Ctx.post (c : Ctx) : List (Option XVal) :=
  match c with
  | .mk _ post => post

-- The same projection without a match auxiliary: the block's casesOn takes one motive
-- per type (Ctx, SetGen, XVal, then the nested List (Option XVal), List SetGen,
-- List (Value × XVal), Option XVal, Value × XVal) and a minor for every constructor.
def Ctx.postR (c : Ctx) : List (Option XVal) :=
  @Ctx.casesOn (fun _ => List (Option XVal)) (fun _ => List (Option XVal))
    (fun _ => List (Option XVal)) (fun _ => List (Option XVal)) (fun _ => List (Option XVal))
    (fun _ => List (Option XVal)) (fun _ => List (Option XVal)) (fun _ => List (Option XVal)) c
    (fun _ post => post)
    (fun _ => []) (fun _ => []) (fun _ _ _ => [])
    (fun _ => []) (fun _ _ _ => []) (fun _ => []) (fun _ => [])
    [] (fun _ _ => [])
    [] (fun _ _ => [])
    [] (fun _ _ => [])
    [] (fun _ => [])
    (fun _ _ => [])

abbrev Frame := List (Option XVal)

def c1 : Ctx := Ctx.mk [Value.int 1] [some (XVal.val (Value.int 2)), none]

def g1 : SetGen := SetGen.filter (SetGen.ofVal (Value.set [])) (Expr.bvar 0) c1

def frame1 : Frame := c1.post

theorem mutual_ctx_single_ctor_door : Nat.beq (c1.env.length + frame1.length) 3 = true := rfl
theorem mutual_ctx_casesOn_door : Nat.beq c1.postR.length 2 = true := rfl

end Model
end Trust
