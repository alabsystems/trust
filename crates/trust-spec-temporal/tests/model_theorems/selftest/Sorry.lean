-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: a theorem closed by sorry. Refused.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Sorry

theorem sorry_thm : 1 = 2 := sorry

end Sorry
end B1bSelftest
end Trust
