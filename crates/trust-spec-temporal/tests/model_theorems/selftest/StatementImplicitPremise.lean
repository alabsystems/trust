-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01b statement selftest (B1B-D30, kernel side), run as ledger-backed entries.
-- Expected, derived from the binder lists:
--   bad:  `{sp : Spec}` (a Spec, data: Type) and `{h : sp.wf = true}` (an Eq: Prop):
--         implicit=2, implicit_premises=1, refused;
--   good: `{sp : Spec}` implicit, `(h : sp.wf = true)` explicit: implicit=1,
--         implicit_premises=0, accepted;
--   pred: `{P : State → Prop}` (a predicate variable: its type `State → Prop` lives in
--         Type, so it is not a premise), `(s : State)`, `(h : P s)` explicit:
--         implicit=1, implicit_premises=0, accepted.
-- B1B-01g (B1B-D58, the B1B-01b verifier's item 4):
--   hidden: its type is the constant `Premised`, which unfolds (delta) to
--         `∀ {h : 1 = 1}, True`: the premise sits behind a definition. The telescope
--         after whnf has one binder, implicit, of type `1 = 1` (an Eq: Prop):
--         implicit=1, implicit_premises=1, refused;
--   lifted: `{h : Lift (1 = 1)}`, where `Lift (P : Prop) : Type` is a structure with
--         one field `down : P` (PLift's shape; Clean's prelude has no PLift): the
--         binder's type lives in `Type` (Sort 1), never Prop: implicit=1,
--         implicit_premises=0, accepted by this kernel side. The known limit B1B-D58
--         records: B1B-01e's text-side TYPE_HEADS grammar is what refuses it.
-- B1B-01e: `Premised` and `Lift` live in the definition module
-- StatementPremiseDefs.lean (same namespace, same constants), since a ledger
-- statement's closure may not reach a constant a theorem module adds.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace StatementImplicitPremise

open Trust.Model

theorem bad {sp : Spec} {h : sp.wf = true} : True := True.intro

theorem good {sp : Spec} (h : sp.wf = true) : True := True.intro

theorem pred {P : State → Prop} (s : State) (h : P s) : P s := h

theorem hidden : Premised := fun {h} => True.intro

theorem lifted {h : Lift (1 = 1)} : True := True.intro

end StatementImplicitPremise
end B1bSelftest
end Trust
