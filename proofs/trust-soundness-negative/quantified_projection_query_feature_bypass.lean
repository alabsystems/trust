-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. The projection-certificate check script appends this
-- declaration to the green model before asking the Clean kernel to reject it.

-- Wrong: an assumption, either parser-owned or API-owned soft assertion, or an
-- objective must make this initial projection-certificate lane ineligible.

def assumption_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      assumptionQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource assumptionQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def parsed_soft_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      parsedSoftQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource parsedSoftQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def native_soft_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      nativeSoftQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource nativeSoftQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def objective_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      objectiveQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource objectiveQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)
