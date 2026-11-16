-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
set_option autoImplicit false

namespace ReachLeastCaller
open Trust.Temporal

-- An ordinary latched device, over all Nat states and the raw step relation.
-- The second branch admits self-loops, including ones outside the reachable set.
def latch : StateMachine Nat :=
  StateMachine.mk (fun s => s = 1) (fun s t => t = 1 ∨ t = s)

theorem latch_safe (s : Nat) (h : Reach latch s) : s = 1 :=
  reach_least Nat latch (fun s => s = 1)
    (fun _ hi => hi)
    (fun _ _ ih hn => Or.elim hn (fun one => one) (fun same => Eq.trans same ih))
    s h

theorem latch_self_loop : Reach latch 1 :=
  Reach.step (Reach.init rfl) (Or.inr rfl)

-- The invariant premise matters: this machine starts at 0, then reaches 1.
def escaping : StateMachine Nat :=
  StateMachine.mk (fun s => s = 0) (fun _ t => t = 1)

theorem escaping_refutes_seed_only : ¬ (∀ s, Reach escaping s → s = 0) :=
  fun all => @Nat.noConfusion False 1 0 (all 1 (Reach.step (Reach.init rfl) rfl))

end ReachLeastCaller
