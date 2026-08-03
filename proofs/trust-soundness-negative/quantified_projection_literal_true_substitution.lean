-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. The authority constructor must require the three exact
-- dependent evidence objects, never three independently chosen Bool values.

def literal_true_substitution_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource exactAuthoredQuery :=
  ProjectionSatAuthority.mint true true true
