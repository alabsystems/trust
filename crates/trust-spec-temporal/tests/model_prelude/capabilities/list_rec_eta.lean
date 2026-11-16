-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- an eta-expanded @List.rec that carries its major premise; the workaround of list_rec_partial.

namespace Trust
namespace Model

def sumList (l : List Nat) : Nat := @List.rec Nat (fun _ => Nat) 0 (fun h _ acc => h + acc) l

theorem sum_door : Nat.beq (sumList [1, 2, 3]) 6 = true := rfl

end Model
end Trust
