-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01b harness selftest (the B1B-01f verifier's item 3): a theorem module whose
-- theorem is sound, beside an unused helper definition closed by `sorry`. Before
-- B1B-01b only the token scan refused it (no theorem reaches the helper, so
-- check_model_theorem passes the theorem). Expected, derived from the definitions:
-- the token scan finds `sorry` (line 19); the kernel sweep over every constant the
-- module adds finds `helper_sorry`'s axiom_deps = {sorryAx} (its value is `sorryAx
-- Nat`, and sorryAx is a non-foundational trust marker, clean-kernel
-- env/axiom_audit.rs); the theorem itself is still checked (1).

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace HelperSorry

def helper_sorry : Nat := sorry

theorem helper_free_true : True := True.intro

end HelperSorry
end B1bSelftest
end Trust
