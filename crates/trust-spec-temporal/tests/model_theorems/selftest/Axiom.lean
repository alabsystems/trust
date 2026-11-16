-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: a module that declares an axiom its theorem never uses.
-- check_model_theorem accepts the theorem (its closure has no axiom), so only the
-- harness's axiom-kind walk over every constant a THEORY module adds, and the token
-- scan behind it, refuse the module (B1B-D06 (c)).

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Axiom

axiom selftest_ax : 1 = 2

theorem axiom_free_true : True := True.intro

end Axiom
end B1bSelftest
end Trust
