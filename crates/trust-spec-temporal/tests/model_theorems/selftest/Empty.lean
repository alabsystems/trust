-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: a module that adds no theorem (one definition only) and has
-- no table row. The runner refuses a module run that checked no theorem.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Empty

def empty_val : Nat := 0

end Empty
end B1bSelftest
end Trust
