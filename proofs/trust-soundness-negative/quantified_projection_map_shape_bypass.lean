-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. Multi-head authority requires a nonempty finite map
-- with one projection binding per stable declaration.

def duplicate_declaration_projection_map_can_mint_wrong :
    CheckedProjectionSemantics Bool duplicateMapSubject :=
  CheckedProjectionSemantics.certify
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    authorityDuplicateProjectionMap authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext rfl rfl
    (fun _ _ => rfl)

def empty_projection_map_can_mint_wrong :
    CheckedProjectionSemantics Bool emptyMapSubject :=
  CheckedProjectionSemantics.certify
    authorityCurrentStamp authorityCurrentQueryEpoch authorityRoots
    ProjectionMap.nil authorityScopeDepth authorityTermCount
    (fun _ => true) trueProjectionMapContext rfl rfl
    (fun _ _ => rfl)
