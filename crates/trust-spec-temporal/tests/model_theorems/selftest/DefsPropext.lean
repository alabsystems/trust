-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest for census rule (d): a definition whose value uses propext
-- directly, with no B1a callee. Its foundational closure is {propext}; the union of its
-- B1a callees' closures is empty; rule (d) refuses it.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace DefsPropext

def defs_uses_propext : Prop :=
  (fun (_ : (True ∧ True) = True) => True)
    (propext (Iff.intro (fun h => And.left h) (fun h => And.intro h h)))

end DefsPropext
end B1bSelftest
end Trust
