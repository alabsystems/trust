-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01b statement selftest (B1B-D07 (d)), moved here from StatementDigestB.lean at
-- B1B-01e: the `abbrev` `carrier_refl` reads, in a definition module, since a ledger
-- statement's closure may not reach a constant a theorem module adds (the B1B-01g
-- verifier's item 5 (2)). Same name, type and value as before, so the recorded
-- digests do not move.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace StatementDigest

abbrev Carrier : Type := Int

end StatementDigest
end B1bSelftest
end Trust
