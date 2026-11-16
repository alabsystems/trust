-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01a harness selftest: a body-less opaque, which Clean lowers to an axiom-kind
-- declaration (the proofIrrel lesson), beside a theorem that does not use it. Refused by
-- the axiom-kind walk (B1B-D06 (c)).

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace Opaque

opaque hidden_prop : Prop

theorem opaque_free_true : True := True.intro

end Opaque
end B1bSelftest
end Trust
