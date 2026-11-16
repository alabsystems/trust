-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01e (the B1B-01g verifier's items 3 and 4): a negative control of the
-- `declaration` cross-check. Clean accepts a `namespace` left open at the end of
-- the file (clean-parser commands.rs, namespace_block: "`end` is optional"), so the
-- module elaborates and its theorem is checked; the harness's lexer reading refuses
-- a scope left open at EOF (fail-closed), so `module_<m>` must report exactly a
-- `declaration` failure.

set_option autoImplicit false

namespace Trust.B1bSelftest.OpenAtEof

theorem open_at_eof : True := True.intro
