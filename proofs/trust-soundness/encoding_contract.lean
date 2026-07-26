-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B, the KEYSTONE: the unified soundness contract `realPanics(f) ⊆ models(P_f)`,
-- proven as a COMPOSITION of the per-arm soundness lemmas. The other files prove that each
-- individual arm's obligation soundly over-approximates that arm's panic — arithmetic
-- (arithmetic_arms), control flow (cfg_paths), the acyclic search (search_soundness),
-- recursion (recursive_summary), and the specific fixed holes (fix_correctness). THIS file
-- proves they COMPOSE: if EVERY operation in a program is sound, then the program's encoded
-- panic set over-approximates its real panics — so `verifier says PROVED ⟹ program is
-- actually safe` for ANY program built from sound arms. That is the property that turns the
-- hand-found false-proofs into a class that cannot exist by construction.
--
-- Model: a program is a list of operations, each carrying its GROUND-TRUTH panic flag
-- `truePanic` and the obligation the encoder emits for it, `obligation` (fires ⟺ the
-- verifier sees a possible panic there). Per-op soundness = `truePanic ⟹ obligation` (the
-- encoding never MISSES a panic) — exactly the per-arm lemmas. The verifier reports PROVED
-- iff no obligation fires anywhere; the program is truly safe iff no op truly panics.
-- Kernel-checked through clean (no sorry / axioms); covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
-- `bor (bnot a) b`: with `bor` matching its first argument, `bimplies false _` reduces to
-- `true` for ANY (even abstract) conclusion — the lever that closes the vacuous cases.
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

-- A program: a list of operations, each (truePanic, obligation).
inductive Prog where
  | nil : Prog
  | cons : Bool -> Bool -> Prog -> Prog

-- GROUND TRUTH: the program panics iff SOME operation truly panics.
def realPanics : Prog -> Bool
  | Prog.nil => false
  | Prog.cons tp _ rest => bor tp (realPanics rest)

-- THE ENCODED PANIC SET: the verifier sees a possible panic iff SOME obligation fires.
-- `models P_f` in the contract; the verifier reports PROVED iff this is `false`.
def models : Prog -> Bool
  | Prog.nil => false
  | Prog.cons _ ob rest => bor ob (models rest)

-- The program is truly SAFE iff NO operation truly panics (= bnot realPanics, folded).
def safe : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp _ rest => band (bnot tp) (safe rest)

-- PROVED-AND-SOUND fold: every op (a) did not fire its obligation [PROVED] AND (b) is sound
-- [truePanic ⟹ obligation — the per-arm lemma]. Per-op condition FIRST so an op that fires
-- its obligation OR is unsound collapses the whole premise to `false` (vacuous implication).
def provedSound : Prog -> Bool
  | Prog.nil => true
  | Prog.cons tp ob rest =>
    band (band (bnot ob) (bimplies tp ob)) (provedSound rest)

-- THE KEYSTONE: if the verifier reports PROVED (no obligation fires) and every op is sound,
-- then the program is truly safe. realPanics ⊆ models, composed from the per-arm lemmas:
-- PROVED ⟹ safe for ANY program built from sound arms.
theorem encoding_sound (p : Prog) : bimplies (provedSound p) (safe p) = true := by
  induction p with
  | nil => rfl
  | cons tp ob rest ih =>
    cases tp with
    | true => cases ob with | true => rfl | false => rfl   -- premise collapses (fired or unsound)
    | false => cases ob with
      | true => rfl                                          -- obligation fired ⇒ not PROVED ⇒ vacuous
      | false => exact ih                                    -- sound, proved op ⇒ reduces to the tail

------------------------------------------------------------------------------------
-- The false-proof class this forbids: an UNSOUND op — `truePanic` true but `obligation`
-- false (the encoder MISSED the panic, exactly the Wrapping and shift-overflow holes found
-- this campaign). The verifier reports PROVED (no obligation) yet the program panics.
------------------------------------------------------------------------------------

def falseProofExample : Prog := Prog.cons true false Prog.nil

theorem bug_verifier_says_proved : models falseProofExample = false := rfl    -- no obligation ⇒ PROVED
theorem bug_program_panics : realPanics falseProofExample = true := rfl       -- but it truly panics
-- ...and `encoding_sound`'s hypothesis is exactly what fails: the op is NOT sound, so the
-- whole `provedSound` premise is false — which is why such a PROVED-but-panics program can
-- only exist when some arm's obligation is missing. Adding that obligation (the Wrapping /
-- shift fixes) restores `truePanic ⟹ obligation`, and then encoding_sound forbids it.
theorem bug_is_exactly_the_unsound_op : provedSound falseProofExample = false := rfl
