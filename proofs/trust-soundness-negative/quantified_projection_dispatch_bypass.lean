-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- RED-CONTROL FRAGMENT. The projection-certificate check script appends this
-- declaration to the green model before asking the Clean kernel to reject it.

-- Wrong: even an EMPTY `check-sat-assuming` is a different authored dispatch;
-- generic-executor and internal-solver dispatches are ineligible as well.

def empty_assuming_dispatch_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      emptyAssumingQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource emptyAssumingQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def generic_executor_dispatch_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      genericExecutorQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource genericExecutorQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)

def internal_solver_dispatch_can_mint_wrong :
    ProjectionSatAuthority Bool authoritySubject currentFreeSource
      internalSolverQueryState :=
  semantic_projection_with_bound_authored_query_mints_sat
    Bool authoritySubject currentFreeSource internalSolverQueryState
    authoritySemanticEvidence currentFreeBindingEvidence
    (CheckedAuthoredPlainHardQuery.certify rfl)
