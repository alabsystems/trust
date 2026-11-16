-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- `variable {S : Type}` (design 40:25) with definitions only.

namespace Trust
namespace Temporal
variable {S : Type}

def Terminal (M : StateMachine S) (s : S) : Prop := ¬ ∃ t, M.next s t

def lastOf (s : S) (rest : List S) : S :=
  @List.rec S (fun _ => S → S) (fun s => s) (fun h _ go _ => go h) rest s

def counter : StateMachine Nat := StateMachine.mk (fun s => s = 0) (fun s t => t = s + 1)

theorem last_door : Nat.beq (lastOf 0 [1, 2, 3]) 3 = true := rfl
theorem terminal_none : ¬ Terminal counter 0 := fun h => h ⟨1, rfl⟩

end Temporal
end Trust
