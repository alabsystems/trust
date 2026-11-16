-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a structure (Ctx) inside a mutual block with inductives (B1A-D21); required pass.

namespace Trust
namespace Model

inductive Value where
  | int : Int → Value
  | set : List Value → Value

inductive Expr where
  | lit : Value → Expr
  | bvar : Nat → Expr

mutual
structure Ctx where
  env  : List Value
  post : List (Option XVal)
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

abbrev Frame := List (Option XVal)

def c1 : Ctx := Ctx.mk [Value.int 1] [some (XVal.val (Value.int 2)), none]

def g1 : SetGen := SetGen.filter (SetGen.ofVal (Value.set [])) (Expr.bvar 0) c1

def frame1 : Frame := c1.post

theorem mutual_structure_ctx_door : Nat.beq (c1.env.length + frame1.length) 3 = true := rfl

end Model
end Trust
