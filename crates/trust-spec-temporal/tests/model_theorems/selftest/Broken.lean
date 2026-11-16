-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: an ill-typed module (1 = 2 by rfl). The test of Broken
-- fails at elaboration. It sits before Indep in the selftest THEORY and neither depends
-- on the other, so the test of Indep passes only because a module's test elaborates its
-- dependency closure and nothing else.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Broken

theorem broken_bad : 1 = 2 := rfl

end Broken
end B1bSelftest
end Trust
