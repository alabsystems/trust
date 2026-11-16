-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: independent of Broken (see Broken.lean); passes.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Indep

theorem indep_true : True := True.intro

end Indep
end B1bSelftest
end Trust
