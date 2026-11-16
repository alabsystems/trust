-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- a List String field (Spec.tokens, B1A-D43); required pass.

namespace Trust
namespace Model

structure Spec where
  vars   : Nat
  tokens : List String

def sp1 : Spec := Spec.mk 2 ["alpha", "beta", "gamma"]

theorem string_field_tokens : sp1.tokens = ["alpha", "beta", "gamma"] := rfl
theorem string_field_door : Nat.beq sp1.tokens.length 3 = true := rfl

end Model
end Trust
