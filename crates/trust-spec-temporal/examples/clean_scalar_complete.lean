-- SPDX-License-Identifier: Apache-2.0 OR MIT

namespace AuthorityExample

def X : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.var "x"
def Zero : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 0
def One : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 1
def Two : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.int 2
def Buggy : Trust.Temporal.FiniteModel.ScalarExpr :=
  Trust.Temporal.FiniteModel.ScalarExpr.constRef "Buggy"

def CompleteAuthority : Trust.Temporal.FiniteModel.ScalarModel :=
  Trust.Temporal.FiniteModel.ScalarModel.mk "CompleteAuthority"
    [Trust.Temporal.FiniteModel.Constant.mk "Buggy" 0]
    [Trust.Temporal.FiniteModel.StateVar.mk "x" 0]
    [Trust.Temporal.FiniteModel.Action.mk "Step"
       (Trust.Temporal.FiniteModel.Guard.when
         (Trust.Temporal.FiniteModel.ScalarExpr.le X Two))
       [Trust.Temporal.FiniteModel.Update.mk "x"
          (Trust.Temporal.FiniteModel.ScalarExpr.add X One)]]
    [Trust.Temporal.FiniteModel.Invariant.mk "Safe"
       (Trust.Temporal.FiniteModel.ScalarExpr.le Buggy X)]

end AuthorityExample
