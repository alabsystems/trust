-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01b statement selftest (the B1A-09 hazard, B1B-D07 (b)): with
-- `set_option autoImplicit false`, an identifier a statement never binds (`sp`) is
-- refused loudly by the elaborator instead of becoming a silent implicit binder.
-- This control is StatementUnbound.lean with auto-bound implicits on, which
-- elaborates: the refusal is the option's, not the statement's.

set_option autoImplicit true

namespace Trust
namespace B1bSelftest
namespace StatementUnboundControl

theorem unbound_eq (x : sp) : x = x := rfl

end StatementUnboundControl
end B1bSelftest
end Trust
