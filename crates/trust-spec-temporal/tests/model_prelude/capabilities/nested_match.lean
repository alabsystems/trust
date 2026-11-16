-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- the nested pattern of nested_ctor_pattern as a nested match; its workaround.

namespace Trust
namespace Model

inductive Inner where
  | a : Nat → Inner
  | b : Inner

inductive Outer where
  | wrap : Inner → Outer
  | none : Outer

def Outer.val : Outer → Nat
  | .wrap i => match i with
    | .a k => k
    | .b => 1
  | .none => 0

theorem pattern_door : Nat.beq (Outer.val (Outer.wrap (Inner.a 7))) 7 = true := rfl

end Model
end Trust
