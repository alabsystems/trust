-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. The projection-certificate check script appends this
-- declaration to the green model before asking the Clean kernel to reject it.

-- Wrong: semantic evidence for subject B cannot authorize subject A, and
-- stopped/resource-limited outcomes are not checked semantic evidence.

def other_subject_semantics_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource exactAuthoredQuery
    authorityOtherSemanticEvidence currentFreeBindingEvidence
    exactAuthoredQueryEvidence

def stopped_check_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource exactAuthoredQuery
    (ProjectionCheckOutcome.stopped Bool authoritySubject)
    currentFreeBindingEvidence exactAuthoredQueryEvidence

def resource_limited_check_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource exactAuthoredQuery
    (ProjectionCheckOutcome.resourceLimit Bool authoritySubject)
    currentFreeBindingEvidence exactAuthoredQueryEvidence
