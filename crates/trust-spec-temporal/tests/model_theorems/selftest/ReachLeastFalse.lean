-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
set_option autoImplicit false

namespace ReachLeastFalse
open Trust.Temporal

def escaping : StateMachine Nat :=
  StateMachine.mk (fun s => s = 0) (fun _ t => t = 1)

-- A seed-only argument cannot prove closure: the 0 -> 1 step falsifies this.
theorem escaping_safe (s : Nat) (h : Reach escaping s) : s = 0 :=
  reach_least Nat escaping (fun s => s = 0)
    (fun _ hi => hi)
    (fun _ _ ih _ => ih)
    s h

end ReachLeastFalse
