-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: the module adds two theorems; the selftest table lists only
-- extra_one, so the exact-set check refuses extra_two.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Extra

theorem extra_one : True := True.intro
theorem extra_two : True := True.intro

end Extra
end B1bSelftest
end Trust
