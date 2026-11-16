-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- Trust.List: the shared list predicates of the Beyond-TLA design (10-executable-
-- semantics.md, "Clean-core conventions", 10:21) and the reducible Bool list helpers
-- the executable presentation uses. Clean source, served to ty by
-- crates/trust-model-prelude and kernel-checked by crates/trust-spec-temporal.
--
-- Membership stays the one inductive of FiniteModel.lean (namespace
-- Trust.Temporal.FiniteModel); `Member` here is its reducible alias, so FiniteModel
-- sources compile unchanged and both names denote one predicate (B1A-D04). The
-- recursive definitions are eta-expanded `List.rec`s that carry their major premise;
-- branching is a raw `Bool.rec` (TASK-STATE 4.8, B1A-D70).

namespace Trust
namespace Temporal

-- `Member value values`: `value` occurs in `values`. The reducible alias of
-- `FiniteModel.Member` (B1A-D04): it unfolds to the inductive, so a `Member` proof is a
-- `FiniteModel.Member` proof and the bridges in both directions are `rfl`.
@[reducible] def Member {α : Type} (value : α) (values : List α) : Prop :=
  FiniteModel.Member value values

-- `Distinct values`: no element of `values` occurs again after itself (Lean's `Nodup`).
-- New here; FiniteModel.lean has neither `Distinct` nor `Nodup` (10:21).
def Distinct {α : Type} (values : List α) : Prop :=
  @List.rec α (fun _ => Prop)
    True
    (fun head tail previous => ¬ Member head tail ∧ previous)
    values

-- `memBy eq value values`: some element `x` of `values` has `eq value x = true`, scanning
-- from the head and stopping at the first hit.
@[reducible] def memBy {α : Type} (eq : α → α → Bool) (value : α) (values : List α) : Bool :=
  @List.rec α (fun _ => Bool)
    false
    (fun head _ found => @Bool.rec (fun _ => Bool) found true (eq value head))
    values

-- `lookupBy eq key entries`: the value of the first entry whose key `k` has
-- `eq key k = true`, or `none`.
@[reducible] def lookupBy {κ β : Type} (eq : κ → κ → Bool) (key : κ) (entries : List (κ × β)) :
    Option β :=
  @List.rec (κ × β) (fun _ => Option β)
    none
    (fun entry _ found => @Bool.rec (fun _ => Option β) found (some entry.snd) (eq key entry.fst))
    entries

-- `nthD values n fallback`: the element at index `n` (from 0), or `fallback` when `values`
-- has at most `n` elements.
@[reducible] def nthD {α : Type} (values : List α) (n : Nat) (fallback : α) : α :=
  @List.rec α (fun _ => Nat → α)
    (fun _ => fallback)
    (fun head _ go n => @Nat.rec (fun _ => α) head (fun k _ => go k) n)
    values n

-- `allB p values`: `p x = true` for every element `x`, stopping at the first `false`.
@[reducible] def allB {α : Type} (p : α → Bool) (values : List α) : Bool :=
  @List.rec α (fun _ => Bool)
    true
    (fun head _ rest => @Bool.rec (fun _ => Bool) false rest (p head))
    values

-- `anyB p values`: `p x = true` for some element `x`, stopping at the first `true`.
@[reducible] def anyB {α : Type} (p : α → Bool) (values : List α) : Bool :=
  @List.rec α (fun _ => Bool)
    false
    (fun head _ rest => @Bool.rec (fun _ => Bool) rest true (p head))
    values

-- `insertBy eq value values`: `values` unchanged when `memBy eq value values`, otherwise
-- `values` with `value` appended, so first-occurrence order is kept.
@[reducible] def insertBy {α : Type} (eq : α → α → Bool) (value : α) (values : List α) :
    List α :=
  @Bool.rec (fun _ => List α) (values ++ [value]) values (memBy eq value values)

-- `lengthEqB xs ys`: the two lists have the same length, compared element by element
-- (no element comparison; it stops at the shorter list's end).
@[reducible] def lengthEqB {α β : Type} (xs : List α) (ys : List β) : Bool :=
  @List.rec α (fun _ => List β → Bool)
    (fun ys => @List.rec β (fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun _ _ go ys => @List.rec β (fun _ => Bool) false (fun _ rest _ => go rest) ys)
    xs ys

end Temporal
end Trust
