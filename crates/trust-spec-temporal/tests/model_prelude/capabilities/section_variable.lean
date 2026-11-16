-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- `variable {S : Type}` (design 40:25) with an inductive (Reach) over it; required pass.

namespace Trust
namespace Temporal
variable {S : Type}

def Terminal (M : StateMachine S) (s : S) : Prop := ¬ ∃ t, M.next s t

inductive Reach (M : StateMachine S) : S → Prop
  | init {s : S} : M.init s → Reach M s
  | step {s t : S} : Reach M s → M.next s t → Reach M t

def counter : StateMachine Nat := StateMachine.mk (fun s => s = 0) (fun s t => t = s + 1)

theorem reach_two : Reach counter 2 :=
  Reach.step (Reach.step (Reach.init rfl) rfl) rfl

end Temporal
end Trust
