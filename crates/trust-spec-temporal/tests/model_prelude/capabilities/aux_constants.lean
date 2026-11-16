-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1A-02b Clean capability matrix II (model_prelude_kernel.rs, clean_capabilities_doors):
-- the auxiliary constants Clean's elaborator generates (casesOn, recOn, below, brecOn,
-- match_N, rec_N, proof_N, ...) and the constants `List ++` elaborates to, classified
-- against Environment::with_prelude(): the input of closure coverage (B1A-D61). Shapes:
-- an enumeration (Kind), a structure (Pair), a nested type (Value), a directly recursive
-- type (Tree), a mutual block (MEven/MOdd) and a recursive Prop former (Leftmost); and
-- definitions whose bodies hold proof terms (boundedTwo, boundedOf), the shape for which
-- a Lean-parity elaborator abstracts a `proof_N` auxiliary (B1A-09).

namespace Trust
namespace Model

-- A nested inductive: its block gets nested auxiliary recursors.
inductive Value where
  | int : Int → Value
  | set : List Value → Value

-- A simple enumeration and a structure.
inductive Kind where
  | a | b

structure Pair where
  fst : Nat
  snd : Kind

-- A match-compiled definition.
def Kind.toNat (k : Kind) : Nat :=
  match k with
  | .a => 0
  | .b => 1

-- A list match.
def headOr (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: _ => x

-- A nested constructor pattern and a `where` helper (both forbidden by B1A-D70; listed
-- here to show which auxiliaries they generate at this pin).
def depth (v : Value) : Nat :=
  match v with
  | .set (.int _ :: _) => 2
  | _ => 0

def total (xs : List Nat) : Nat := go xs 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: rest, acc => go rest (acc + x)

-- `if` on a Bool and `&&`.
def pick (b c : Bool) : Nat := if b && c then 1 else 0

-- `List ++`.
def appendAll (xs ys : List Nat) : List Nat := xs ++ ys

-- A directly recursive inductive: not mutual, not nested, not a Prop former. This is the
-- one shape for which Clean generates `below` and `brecOn` (clean-kernel
-- env/inductive_builder.rs Pass 3, env/inductive_below.rs `should_generate_below`:
-- PUnit and PProd present, the type recursive, not a Prop former).
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

-- Structural recursion by equations over it: compiled to `Tree.rec` in the body, not
-- to `Tree.brecOn`.
def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => Tree.size l + Tree.size r

-- Mutual control: two types recursive through each other.
mutual
inductive MEven where
  | zero : MEven
  | succ : MOdd → MEven
inductive MOdd where
  | succ : MEven → MOdd
end

-- Prop-former control: a recursive inductive predicate.
inductive Leftmost : Tree → Prop where
  | leaf : Leftmost Tree.leaf
  | node : (l r : Tree) → Leftmost l → Leftmost (Tree.node l r)

-- Nested proofs: a Subtype literal whose proof is a term (`rfl`), at the top of the
-- body and under a binder (in both minors of a `Bool.rec`). Lean abstracts each such
-- proof into `boundedTwo.proof_1`, `boundedOf.proof_1`, ...; measured here.
def boundedTwo : Subtype (fun n : Nat => Nat.ble n 3 = true) := Subtype.mk 2 rfl

def boundedOf (b : Bool) : Subtype (fun n : Nat => Nat.ble n 3 = true) :=
  @Bool.rec (fun _ => Subtype (fun n : Nat => Nat.ble n 3 = true))
    (Subtype.mk 0 rfl) (Subtype.mk 3 rfl) b

theorem aux_append : Nat.beq (appendAll [1, 2] [3]).length 3 = true := rfl
theorem aux_match : Nat.beq (Kind.toNat Kind.b) 1 = true := rfl
theorem aux_pattern : Nat.beq (depth (Value.set [Value.int 1])) 2 = true := rfl
theorem aux_where : Nat.beq (total [1, 2, 3]) 6 = true := rfl
theorem aux_if : Nat.beq (pick true true) 1 = true := rfl
theorem aux_list_match : Nat.beq (headOr [4, 5]) 4 = true := rfl
theorem aux_projection : Nat.beq (Pair.mk 3 Kind.a).fst 3 = true := rfl
theorem aux_nested_proof : Nat.beq boundedTwo.val 2 = true := rfl
theorem aux_nested_proof_binder : Nat.beq (boundedOf true).val 3 = true := rfl
theorem aux_tree_size : Nat.beq (Tree.size (Tree.node Tree.leaf (Tree.node Tree.leaf Tree.leaf))) 3 = true := rfl

end Model
end Trust
