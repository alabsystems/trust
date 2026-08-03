-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. `scripts/check_ay_projection_certificate.sh` appends
-- this declaration to the green quantified-projection model before checking.
-- It is deliberately not a standalone proof.

-- Each declaration below attempts to manufacture binding evidence with `rfl`.
-- Every modeled identity mismatch and every non-free declaration kind reduces
-- to false, so all attempts must fail independently.

def missing_source_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject missingSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject missingSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def stale_source_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject staleSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject staleSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def foreign_source_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject foreignSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject foreignSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def changed_root_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject changedRootSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject changedRootSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def replacement_id_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject replacementDeclarationSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject replacementDeclarationSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def changed_signature_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject changedSignatureSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject changedSignatureSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def defined_declaration_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject definedDeclarationSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject definedDeclarationSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def adopted_declaration_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject adoptedDeclarationSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject adoptedDeclarationSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def datatype_constructor_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject datatypeConstructorSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject datatypeConstructorSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def datatype_selector_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject datatypeSelectorSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject datatypeSelectorSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def datatype_tester_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject datatypeTesterSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject datatypeTesterSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def theory_declaration_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject theoryDeclarationSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject theoryDeclarationSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

def internal_declaration_binding_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject internalDeclarationSource
      exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject internalDeclarationSource exactAuthoredQuery
    authoritySemanticEvidence (CheckedSourceBinding.certify rfl)
    exactAuthoredQueryEvidence

-- Wrong in the other direction: already-valid evidence is indexed by
-- `currentFreeSource` and cannot be transported to a stale live-source index.
def current_binding_evidence_can_cross_live_index_wrong :
    ProjectionSatAuthority Bool authoritySubject staleSource exactAuthoredQuery :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject staleSource exactAuthoredQuery
    authoritySemanticEvidence currentFreeBindingEvidence
    exactAuthoredQueryEvidence
