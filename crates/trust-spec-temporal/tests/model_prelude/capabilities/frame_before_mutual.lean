-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- `abbrev Frame := List (Option XVal)` before the mutual block declaring XVal (design 10:230); expected failure.

namespace Trust
namespace Model

inductive Value where
  | int : Int → Value

inductive Expr where
  | lit : Value → Expr

abbrev Frame := List (Option XVal)

mutual
inductive Ctx where
  | mk : List Value → Frame → Ctx
inductive XVal where
  | val    : Value → XVal
  | lazyFn : Expr → Ctx → XVal
end

def c1 : Ctx := Ctx.mk [Value.int 1] [some (XVal.val (Value.int 2)), none]

def Ctx.post (c : Ctx) : Frame :=
  match c with
  | .mk _ post => post

theorem frame_door : Nat.beq c1.post.length 2 = true := rfl

end Model
end Trust
