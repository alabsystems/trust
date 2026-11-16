-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01e (the B1B-01g verifier's item 4): Clean's scope rule (clean-parser
-- grammar/decl/commands.rs, namespace_block and try_consume_end_name): `end X`
-- closes as many components of the innermost `namespace` as X has, when X is a
-- component-wise suffix of it. So `end PartialEnd` below leaves
-- `Trust.B1bSelftest` open, and `after_partial` is `Trust.B1bSelftest.after_partial`
-- (derived from that rule, not read off a run). The harness's lexer reading must
-- agree with the elaborator: no `declaration` failure, both theorems checked.

set_option autoImplicit false

namespace Trust.B1bSelftest.PartialEnd

theorem inside_partial : True := True.intro

end PartialEnd

theorem after_partial : True := True.intro

end Trust.B1bSelftest
