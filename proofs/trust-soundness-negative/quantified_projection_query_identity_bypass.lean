-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. The projection-certificate check script appends this
-- declaration to the green model before asking the Clean kernel to reject it.

-- These preserve the semantic subject while changing one query-binding field.
-- In particular, `repeatedQueryState` differs ONLY in its public
-- QueryAuthorityEpoch: identical consecutive `check-sat` commands cannot reuse
-- one another's permit.

def stale_source_epoch_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      staleSourceEpochQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource staleSourceEpochQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def repeated_query_epoch_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      repeatedQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource repeatedQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_roots_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedRootsQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedRootsQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def reordered_roots_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      reorderedRootsQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource reorderedRootsQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def short_roots_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      shortRootsQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource shortRootsQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def long_roots_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      longRootsQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource longRootsQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def replacement_declaration_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      replacementDeclarationQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource replacementDeclarationQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_result_signature_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedResultSignatureQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedResultSignatureQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_argument_signature_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedArgumentSignatureQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedArgumentSignatureQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def reordered_argument_signature_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      reorderedArgumentSignatureQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource reorderedArgumentSignatureQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_arity_signature_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedAritySignatureQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedAritySignatureQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_selector_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedSelectorQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedSelectorQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_application_pattern_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedPatternQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedPatternQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_scope_depth_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedScopeDepthQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedScopeDepthQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def changed_term_count_query_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      changedTermCountQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource changedTermCountQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

-- Wrong in the other direction: the valid query evidence is indexed by the
-- current query and cannot be transported to a repeated-query epoch.
def exact_query_evidence_can_cross_query_index_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      repeatedQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource repeatedQueryState
    authoritySemanticEvidence currentFreeBindingEvidence exactAuthoredQueryEvidence
