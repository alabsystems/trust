-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
set_option autoImplicit false

namespace Trust
namespace Temporal

-- Any predicate containing the initial states and preserved by the original
-- transition relation holds on every Reach derivation. No stuttering filter or
-- restriction on the state carrier is needed.
theorem reach_least
    (S : Type) (M : StateMachine S) (R : S → Prop)
    (hinit : ∀ s, M.init s → R s)
    (hstep : ∀ s t, R s → M.next s t → R t)
    (s : S) (h : Reach M s) : R s :=
  @Reach.rec S M
    (fun s _ => R s)
    (fun {s} hi => hinit s hi)
    (fun {s t} _ hn ih => hstep s t ih hn)
    s h

end Temporal
end Trust
