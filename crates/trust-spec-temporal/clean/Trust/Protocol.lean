-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Protocol: short names for writing a finite model and its claims in
-- an island.  Every name for a model here is an ordinary definition that
-- unfolds to the constructors of `Trust.FiniteModel` and
-- `Trust.FiniteModelCheck`, so it carries no authority of its own: the
-- compiler detects and checks a model written with it exactly as one written
-- with the constructors.  (`Binding`, the data that ties a model to the Rust
-- code beside it, is `Trust.Binding`'s and is in scope here too.)
--
--   open Trust.Protocol
--   def M : Trust.Temporal.FiniteModel.ScalarModel :=
--     machine "Counter" []
--       [var "x" 0]
--       [act "Inc" (v "x" ≺ n 3) ["x" ≔ v "x" ⊞ n 1]]
--       [inv "Bounded" (v "x" ≼ n 3)]
--   def Reaches : Trust.Temporal.FiniteModel.ScalarProgress :=
--     progress M (v "x" ≐ n 3) ["Inc"] []
--
-- The operators are model expressions, not propositions, so they are spelled
-- apart from Clean's own: `⊞ ⊟` add and subtract, `≐ ≢` equal and unequal,
-- `≼ ≺ ≻ ≽` compare, `⋏ ⋎` and and or, `≔` updates a variable.
--
-- THE MODEL LANGUAGE IS OVER THE NATURAL NUMBERS: `⊟` stops at zero, so
-- `a ≼ b ⊟ n 1` is true at a = b = 0.  Write `a ≺ b` (which is `b ≻ a`) or
-- `a ⊞ n 1 ≼ b` instead; the compiler warns at a subtraction that stops at
-- zero on a reachable state.

namespace Trust
namespace Protocol

-- the value of a state variable, a number, a named constant
def v (name : String) : _root_.Trust.Temporal.FiniteModel.ScalarExpr :=
  _root_.Trust.Temporal.FiniteModel.ScalarExpr.var name
def n (value : Nat) : _root_.Trust.Temporal.FiniteModel.ScalarExpr :=
  _root_.Trust.Temporal.FiniteModel.ScalarExpr.int value
def k (name : String) : _root_.Trust.Temporal.FiniteModel.ScalarExpr :=
  _root_.Trust.Temporal.FiniteModel.ScalarExpr.constRef name

-- `a` below `b`, and `a` at least `b`, with no subtraction
def lt (a b : _root_.Trust.Temporal.FiniteModel.ScalarExpr) : _root_.Trust.Temporal.FiniteModel.ScalarExpr :=
  _root_.Trust.Temporal.FiniteModel.ScalarExpr.gt b a
def ge (a b : _root_.Trust.Temporal.FiniteModel.ScalarExpr) : _root_.Trust.Temporal.FiniteModel.ScalarExpr :=
  _root_.Trust.Temporal.FiniteModel.ScalarExpr.le b a
-- `c`'s value is `a` when `c` holds, else `b`
def cond (c a b : _root_.Trust.Temporal.FiniteModel.ScalarExpr) : _root_.Trust.Temporal.FiniteModel.ScalarExpr :=
  _root_.Trust.Temporal.FiniteModel.ScalarExpr.ite c a b
infixl:65 " ⊞ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.add
infixl:65 " ⊟ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.sub
infix:50 " ≐ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.eq
infix:50 " ≢ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.neq
infix:50 " ≼ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.le
infix:50 " ≻ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.gt
infix:50 " ≺ " => _root_.Trust.Protocol.lt
infix:50 " ≽ " => _root_.Trust.Protocol.ge
infixr:35 " ⋏ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.and
infixr:30 " ⋎ " => _root_.Trust.Temporal.FiniteModel.ScalarExpr.or

-- a state variable and its initial value; a named constant
def var (name : String) (init : Nat) : _root_.Trust.Temporal.FiniteModel.StateVar :=
  _root_.Trust.Temporal.FiniteModel.StateVar.mk name init
def param (name : String) (value : Nat) : _root_.Trust.Temporal.FiniteModel.Constant :=
  _root_.Trust.Temporal.FiniteModel.Constant.mk name value

-- one update of an action: `"x" ≔ v "x" ⊞ n 1`
def set (name : String) (value : _root_.Trust.Temporal.FiniteModel.ScalarExpr) :
    _root_.Trust.Temporal.FiniteModel.Update :=
  _root_.Trust.Temporal.FiniteModel.Update.mk name value
infix:40 " ≔ " => _root_.Trust.Protocol.set

-- an action: its name, its guard and its updates (the rest keep their values)
def act (name : String) (guard : _root_.Trust.Temporal.FiniteModel.ScalarExpr)
    (updates : List _root_.Trust.Temporal.FiniteModel.Update) : _root_.Trust.Temporal.FiniteModel.Action :=
  _root_.Trust.Temporal.FiniteModel.Action.mk name (_root_.Trust.Temporal.FiniteModel.Guard.when guard) updates

-- an action whose guard always holds
def always (name : String) (updates : List _root_.Trust.Temporal.FiniteModel.Update) :
    _root_.Trust.Temporal.FiniteModel.Action :=
  _root_.Trust.Temporal.FiniteModel.Action.mk name _root_.Trust.Temporal.FiniteModel.Guard.always updates

-- an invariant: its name and what holds in every reachable state
def inv (name : String) (holds : _root_.Trust.Temporal.FiniteModel.ScalarExpr) :
    _root_.Trust.Temporal.FiniteModel.Invariant :=
  _root_.Trust.Temporal.FiniteModel.Invariant.mk name holds

-- the model: its name, constants, variables, actions and invariants
def machine (name : String) (params : List _root_.Trust.Temporal.FiniteModel.Constant)
    (vars : List _root_.Trust.Temporal.FiniteModel.StateVar)
    (acts : List _root_.Trust.Temporal.FiniteModel.Action)
    (invs : List _root_.Trust.Temporal.FiniteModel.Invariant) : _root_.Trust.Temporal.FiniteModel.ScalarModel :=
  _root_.Trust.Temporal.FiniteModel.ScalarModel.mk name params vars acts invs

-- a progress claim: on every run fair to the actions named in `weak`
-- (weakly) and `strong` (strongly), `goal` holds again and again
def progress (model : _root_.Trust.Temporal.FiniteModel.ScalarModel)
    (goal : _root_.Trust.Temporal.FiniteModel.ScalarExpr) (weak strong : List String) :
    _root_.Trust.Temporal.FiniteModel.ScalarProgress :=
  _root_.Trust.Temporal.FiniteModel.ScalarProgress.mk model goal weak strong

-- `Binding` and `binds` (data that ties a model to the Rust code beside it)
-- are defined in `Trust.Binding`, which this module is served on top of: an
-- island that declares only a binding imports that small module alone.

end Protocol
end Trust
