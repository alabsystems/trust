-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT for quantified_projection_certificate.lean.
--
-- The proof script and Trust front-door test append this declaration to the
-- exact green model. A checker that accepted merely because the premise
-- matched could manufacture semantic evidence for the false conclusion.

-- Deliberately impossible: for every tuple, the premise is true but
-- `reduceBool (falseContext ...)` is false. The exact semantic constructor
-- therefore requires a proof of `false = true`.
def accept_without_conclusion_wrong :
    CheckedProjectionSemantics Bool falseSemanticSubject :=
  CheckedProjectionSemantics.certify
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    authorityProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) falseProjectionMapContext rfl rfl
    (fun _ _ => rfl)
