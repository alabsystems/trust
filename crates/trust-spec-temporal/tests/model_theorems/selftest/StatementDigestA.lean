-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01b statement selftest (B1B-D07 (d)): `carrier_refl`'s text is byte-identical
-- in StatementDigestA.lean and StatementDigestB.lean; only the `abbrev` it reads
-- differs (Nat here, Int there; the `abbrev` lives in the definition module
-- StatementCarrierNat.lean, B1B-01e: a ledger statement reads no constant a theorem
-- module adds). The statement digest must differ between the two
-- (it covers the definitions a statement reads), and be stable across runs.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace StatementDigest


theorem carrier_refl (x : Carrier) : x = x := rfl

end StatementDigest
end B1bSelftest
end Trust
