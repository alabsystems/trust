-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: the selftest table lists missing_one and missing_two as
-- proved; the module adds only missing_one, so the exact-set check refuses.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Missing

theorem missing_one : True := True.intro

end Missing
end B1bSelftest
end Trust
