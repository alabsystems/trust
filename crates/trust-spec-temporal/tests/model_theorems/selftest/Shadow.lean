-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01e (the B1B-01g verifier's item 5 (2)): a theorem module whose own definition
-- shadows a vocabulary name. `shadowed`'s statement text `(v : Value)` resolves to the
-- module-local `Value` (the innermost namespace wins), so its elaborated closure
-- reaches a constant this theorem module adds: refused as `statement reads module
-- constant` (ledger-backed). `helper_reads_local` reads the same local constant but is
-- a helper (ledger id `-`), and `unshadowed` reads only `Nat`: both are checked.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Shadow

def Value : Type := Nat

theorem shadowed (v : Value) : v = v := rfl

theorem helper_reads_local (v : Value) : v = v := rfl

theorem unshadowed (n : Nat) : n = n := rfl

end Shadow
end B1bSelftest
end Trust
