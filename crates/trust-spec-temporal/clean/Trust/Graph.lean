-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Graph: the raw state-graph vocabulary of the Beyond-TLA design
-- (40-graph.md, section 1.1, 40:28-68): Terminal, Reach, Star, MaxPath, Chain, lastOf,
-- FirstAtEnd and WitnessPath, generic over `StateMachine S`. Clean source, served to
-- ty by crates/trust-model-prelude and kernel-checked by crates/trust-spec-temporal.
-- Delivered in B1a because B1a's claims need Reach, Chain and WitnessPath (B1A-D05).
--
-- Two departures of form, none of meaning, both measured at trust's Clean pin by the
-- B1A-02a capability matrix (B1A-D70):
-- * The design writes the file under `variable {S : Type}` (40:25). An inductive under
--   `variable` is refused (capabilities/section_variable.lean), so every declaration
--   here takes its own explicit `{S : Type}` binder, which is the binder `variable`
--   would have added (capabilities/section_variable_explicit.lean).
-- * Chain, lastOf and FirstAtEnd are written by two-argument pattern recursion in the
--   design (40:55-65). Here each is the eta-expanded `List.rec` over the list with the
--   state argument threaded through the motive (`S → _`), the form the cost discipline
--   and the value pins use; each reduces exactly as the design's equations, which the
--   sanity file checks case by case (tests/model_prelude/sanity/list_graph.lean).

namespace Trust
namespace Temporal

-- Graph notions use the raw step relation. A self-loop is a step; a state with no
-- successor is terminal (the TLC/MCC deadlock). `Runs` keeps TLA+'s stuttering; this file
-- adds none.
def Terminal {S : Type} (M : StateMachine S) (s : S) : Prop := ¬ ∃ t, M.next s t

inductive Reach {S : Type} (M : StateMachine S) : S → Prop
  | init {s : S} : M.init s → Reach M s
  | step {s t : S} : Reach M s → M.next s t → Reach M t

inductive Star {S : Type} (M : StateMachine S) : S → S → Prop
  | refl (s : S) : Star M s s
  | tail {s t u : S} : Star M s t → M.next t u → Star M s u

-- A maximal path steps at every position, or has reached a terminal state and repeats it.
def MaxPath {S : Type} (M : StateMachine S) (s : S) (p : Behavior S) : Prop :=
  p 0 = s ∧ ∀ n, M.next (p n) (p (n + 1)) ∨ (Terminal M (p n) ∧ p (n + 1) = p n)

-- `Chain M s p`: `s` steps to the first state of `p`, and each state of `p` to the next.
--   Chain M _ []          = True
--   Chain M s (t :: rest) = M.next s t ∧ Chain M t rest
def Chain {S : Type} (M : StateMachine S) (s : S) (p : List S) : Prop :=
  @List.rec S (fun _ => S → Prop)
    (fun _ => True)
    (fun t _ go s => M.next s t ∧ go t)
    p s

-- `lastOf s p`: the last state of `s :: p`.
--   lastOf s []          = s
--   lastOf _ (t :: rest) = lastOf t rest
def lastOf {S : Type} (s : S) (p : List S) : S :=
  @List.rec S (fun _ => S → S)
    (fun s => s)
    (fun t _ go _ => go t)
    p s

-- `FirstAtEnd Y s p`: Y holds at no position of `s :: p` before the last.
--   FirstAtEnd Y _ []          = True
--   FirstAtEnd Y s (t :: rest) = ¬ Y s ∧ FirstAtEnd Y t rest
def FirstAtEnd {S : Type} (Y : S → Prop) (s : S) (p : List S) : Prop :=
  @List.rec S (fun _ => S → Prop)
    (fun _ => True)
    (fun t _ go s => ¬ Y s ∧ go t)
    p s

-- An initial state followed by steps.
def WitnessPath {S : Type} (M : StateMachine S) (w : List S) : Prop :=
  ∃ s₀ p, w = s₀ :: p ∧ M.init s₀ ∧ Chain M s₀ p

end Temporal
end Trust
