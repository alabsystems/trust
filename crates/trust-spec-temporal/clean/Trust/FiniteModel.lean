-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- A kernel-elaborated, user-authored replacement for the well-formed,
-- certifiable scalar fragment of `trust_model!`.  This is deliberately a DATA
-- vocabulary: the Rust bridge
-- decodes the value of a `ScalarModel` definition after Clean elaboration and
-- derives ty's private TLA+ input from that value.  It is not, by itself, a
-- proof that the generated input denotes `Trust.Temporal.StateMachine`; that
-- behavior-level bridge remains a separately graded obligation.

namespace Trust
namespace Temporal
namespace FiniteModel

-- The scalar expression union accepted by the old model value.  Arithmetic is
-- over the nonnegative fragment used by the macro surface.  References are
-- names, just as they were in `trust_model!`; the consumer rejects missing,
-- duplicate, or cross-sort names before generating a model. `ite` preserves the
-- common scalar sort of its branches; the bridge rejects mixed-sort branches.
inductive ScalarExpr where
  | int : Nat → ScalarExpr
  | var : String → ScalarExpr
  | constRef : String → ScalarExpr
  | add : ScalarExpr → ScalarExpr → ScalarExpr
  | sub : ScalarExpr → ScalarExpr → ScalarExpr
  | gt : ScalarExpr → ScalarExpr → ScalarExpr
  | le : ScalarExpr → ScalarExpr → ScalarExpr
  | eq : ScalarExpr → ScalarExpr → ScalarExpr
  | neq : ScalarExpr → ScalarExpr → ScalarExpr
  | or : ScalarExpr → ScalarExpr → ScalarExpr
  | and : ScalarExpr → ScalarExpr → ScalarExpr
  | ite : ScalarExpr → ScalarExpr → ScalarExpr → ScalarExpr
  | iff : ScalarExpr → ScalarExpr → ScalarExpr
  | forallIn : String → ScalarExpr → ScalarExpr → ScalarExpr → ScalarExpr
  | bool : Bool → ScalarExpr

structure Constant where
  name : String
  value : Nat

structure StateVar where
  name : String
  init : Nat

structure Update where
  var : String
  value : ScalarExpr

inductive Guard where
  | always
  | when : ScalarExpr → Guard

structure Action where
  name : String
  guard : Guard
  updates : List Update

structure Invariant where
  name : String
  value : ScalarExpr

structure ScalarModel where
  name : String
  constants : List Constant
  variables : List StateVar
  actions : List Action
  invariants : List Invariant

end FiniteModel
end Temporal
end Trust
