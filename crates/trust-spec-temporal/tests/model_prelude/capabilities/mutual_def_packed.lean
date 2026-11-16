-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02a Clean capability matrix (model_prelude_kernel.rs, clean_capabilities_features):
-- the same mutual recursion as one fuel-indexed function over a tagged job (B1A-D07); the workaround of mutual_def_multi_arg.

namespace Trust
namespace Model

-- The mutual pair of mutual_def_multi_arg.lean as one fuel-indexed function over
-- a tagged job (B1A-D07): `go` is the recursive call, the fuel a Nat.rec.
inductive Job where
  | e : List Nat → Job
  | l : List Nat → Job

def step (go : Job → Nat) (j : Job) : Nat :=
  @Job.rec (fun _ => Nat)
    (fun xs => 1 + go (Job.l xs))
    (fun xs => @List.rec Nat (fun _ => Nat) 0 (fun x rest _ => x + go (Job.e rest)) xs)
    j

def run (fuel : Nat) : Job → Nat :=
  @Nat.rec (fun _ => Job → Nat) (fun _ => 0) (fun _ go => step go) fuel

def sumE (fuel : Nat) (xs : List Nat) : Nat := run fuel (Job.e xs)

theorem mutual_door : Nat.beq (sumE 20 [1, 2, 3]) 10 = true := rfl

end Model
end Trust
