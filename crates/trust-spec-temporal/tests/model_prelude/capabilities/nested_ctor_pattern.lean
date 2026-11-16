-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a nested constructor pattern in an equation; expected failure (Sep 19 CLI).

namespace Trust
namespace Model

inductive Inner where
  | a : Nat → Inner
  | b : Inner

inductive Outer where
  | wrap : Inner → Outer
  | none : Outer

def Outer.val : Outer → Nat
  | .wrap (.a k) => k
  | .wrap .b => 1
  | .none => 0

theorem pattern_door : Nat.beq (Outer.val (Outer.wrap (Inner.a 7))) 7 = true := rfl

end Model
end Trust
