-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.Binding: the data that ties a model to the Rust code beside it
-- (`Binding`, `Seal`).  It imports nothing, so an island that declares only
-- a binding or a seal pays for no model library:
--
--   import Trust.Binding
--   open Trust.Protocol
--   def policy : Trust.Protocol.Binding :=
--     binds "config.harness" ["HarnessPolicyObserved"] []
--
-- `Trust.Protocol` is served on top of this module, so an island that
-- writes its model with that notation has `Binding` in scope already.

namespace Trust
namespace Protocol

-- A binding between a model and the code beside it.  The Rust field at
-- `path` (a field path on the type a message consumer runs on:
-- `"config.harness"` for `App.config.harness`) is written only from the arms
-- for the message variants in `arms` (`"HarnessPolicyObserved"`, or
-- `"Wake::HarnessPolicyObserved"`), except by the fns in `carriedBy` (a fn's
-- name, or `"Type::method"`), which the author says only carry the value
-- over.  It is data, with no proof: the compiler finds every write of the
-- field in the crate and fails the build at the binding when one can be
-- reached from anywhere else.
--
--   def policy : Trust.Protocol.Binding :=
--     binds "config.harness" ["HarnessPolicyObserved"] []
structure Binding where
  path : String
  arms : List String
  carriedBy : List String

def binds (path : String) (arms carriedBy : List String) : _root_.Trust.Protocol.Binding :=
  _root_.Trust.Protocol.Binding.mk path arms carriedBy

-- A seal on a type of this crate: the state a model speaks of, kept in a
-- type of its own.  A field of a value of `type_` is changed only while one
-- of `writers` runs; a value of it is built only in `makers`, which are
-- called only from `madeBy`; and no value that owns one is put over another,
-- except by the fns of other crates in `trusts`.  It is data, with no proof,
-- and unlike `Binding` the compiler follows no pointer to check it: every
-- condition is read off one statement and its types, and Rust's own rules
-- (privacy, the borrow checker) carry the rest.  Safe code only.
--
--   def cell : Trust.Protocol.Seal :=
--     seals "Generational" ["offer"] ["new"] ["App::new"] []
structure Seal where
  type_ : String
  writers : List String
  makers : List String
  madeBy : List String
  trusts : List String

def seals (type_ : String) (writers makers madeBy trusts : List String) :
    _root_.Trust.Protocol.Seal :=
  _root_.Trust.Protocol.Seal.mk type_ writers makers madeBy trusts

end Protocol
end Trust
