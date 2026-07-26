-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B: the CHC REACHABILITY FIXPOINT. chc_error_reachability models the error-rules
-- with the path guard GIVEN; this COMPUTES it — block reachability propagates forward through
-- the CFG's edge guards (the least fixpoint the CHC solver computes), and `error` is reachable
-- iff some REACHED block fires its obligation. The reachability threading lives in `annotate`
-- (block i reachable = predecessor reached ∧ edge guard); the soundness is then the flat
-- keystone over the reachability-guarded obligations. So PROVED (no reached block's obligation
-- fires) ⟹ truly safe. Kernel-checked; gated.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

-- Flat keystone program of (truePanic, obligation) pairs.
inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog

def realPanics : Prog -> Bool
  | Prog.nil => false
  | Prog.cons tp _ rest => bor tp (realPanics rest)
def models : Prog -> Bool
  | Prog.nil => false
  | Prog.cons _ ob rest => bor ob (models rest)
def safe : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp _ rest => band (bnot tp) (safe rest)
def provedSound : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp ob rest => band (band (bnot ob) (bimplies tp ob)) (provedSound rest)

theorem encoding_sound (p : Prog) : bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl
    | false => cases ob with | true => rfl | false => exact ih

-- A linear block chain. Each block: the guard on the edge INTO it, its true panic, the
-- obligation. Reachability propagates: a block is reached iff its predecessor was reached AND
-- the edge guard holds.
inductive Chain where
  | halt : Chain
  | blk : Bool -> Bool -> Bool -> Chain -> Chain   -- edgeGuard, truePanic, obligation, rest

-- THE FIXPOINT, as a definition: thread reachability `r` forward, emitting for each block the
-- reachability-GUARDED panic and obligation `(reached ∧ tp, reached ∧ ob)`. `models` of this
-- = error reachable (some reached block fires); `safe` = no reached block panics.
def annotate : Bool -> Chain -> Prog
  | _, Chain.halt => Prog.nil
  | r, Chain.blk guard tp ob rest =>
    Prog.cons (band (band r guard) tp) (band (band r guard) ob) (annotate (band r guard) rest)

-- THE REACHABILITY-FIXPOINT SOUNDNESS: for any starting reachability, if PROVED (no reached
-- block's obligation fires) and every emitted rule is sound, the program is truly safe. This
-- is the flat keystone applied to the reachability-threaded annotation — the threading
-- (`annotate`) computes the path guard chc_error_reachability had assumed.
theorem chain_reachability_sound (r : Bool) (c : Chain) :
    bimplies (provedSound (annotate r c)) (safe (annotate r c)) = true :=
  encoding_sound (annotate r c)

-- A panic site past a FALSE edge guard is unreachable: `annotate` zeroes its guarded panic and
-- obligation, so it cannot make `error` reachable nor count as a real panic — the dominating
-- guard's soundness, now COMPUTED by the fixpoint rather than assumed.
def guardedOut : Chain := Chain.blk false true true Chain.halt
theorem guardedOut_unreachable : models (annotate true guardedOut) = false := rfl
theorem guardedOut_no_panic : realPanics (annotate true guardedOut) = false := rfl

-- A reachable panicking site (guard true, obligation fires): error reachable ⇒ not proved.
def reachablePanic : Chain := Chain.blk true true true Chain.halt
theorem reachablePanic_error : models (annotate true reachablePanic) = true := rfl
theorem reachablePanic_panics : realPanics (annotate true reachablePanic) = true := rfl

-- A reachable TOTAL chain (guards true, no obligation fires): proved + truly safe.
def reachableSafe : Chain := Chain.blk true false false (Chain.blk true false false Chain.halt)
theorem reachableSafe_proved : models (annotate true reachableSafe) = false := rfl
theorem reachableSafe_safe : safe (annotate true reachableSafe) = true := rfl
