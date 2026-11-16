-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: a theorem through Classical.em, whose kernel proof
-- (Diaconescu, clean-kernel classical_em_proof.rs) uses Classical.choice. The census
-- refuses it with classical=- and accepts it when the row's classical column names a
-- decision (B1B-D06 (b)).

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Classical

theorem em_nat (n : Nat) : n = 0 ∨ ¬ (n = 0) := Classical.em (n = 0)

end Classical
end B1bSelftest
end Trust
