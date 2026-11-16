-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01g statement selftest (B1B-D58), moved here from StatementImplicitPremise.lean
-- at B1B-01e: the definitions the `hidden` and `lifted` statements read, in a
-- definition module, since a ledger statement's closure may not reach a constant a
-- theorem module adds (the B1B-01g verifier's item 5 (2)). Same names and bodies.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace StatementImplicitPremise

abbrev Premised : Prop := ∀ {h : 1 = 1}, True

structure Lift (P : Prop) : Type where
  down : P

end StatementImplicitPremise
end B1bSelftest
end Trust
