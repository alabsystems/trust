-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01b harness selftest for the definitions runner on kernel-generated constants
-- (the B1B-01f verifier's item 4): an inductive (its constructors, recursor and the
-- auxiliary eliminators Clean generates) and a structure (its constructor and
-- projections), plus a plain definition over them. None reaches an axiom of its own:
-- every constant is built by the kernel from the declaration or is a plain `def`, so
-- each must pass axiom_deps, the certification audit and census rule (d). A refusal
-- here would be a false refusal of exactly the shape B1B-03 (Branching, Ctl) and
-- B1B-06 (Petri) will declare, measured before those rows rely on the runner.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace DefsInductive

inductive Light where
  | red
  | green

structure Pair where
  fst : Nat
  snd : Nat

def defs_swap (p : Pair) : Pair := Pair.mk p.snd p.fst

def defs_flip (l : Light) : Light := Light.casesOn l Light.green Light.red

end DefsInductive
end B1bSelftest
end Trust
