-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Apex Step B / Rung 4: the UNBOUNDED CHC PREFIXPOINT (Tarski direction) — the soundness of the
-- CHC encoding for derivations of ARBITRARY depth, i.e. WITH loops / general recursion in the
-- rule graph. chc_prefixpoint_acyclic.lean closed the bounded (acyclic) case by composing the
-- one-step lemma to fixed depths; this proves it for ALL derivations at once:
--
--   deriv_prefixpoint : ∀ d, derivValid m d ⟹ holds m (derivHead d)
--
-- "every relation a valid derivation derives holds in the model m" — the least-fixpoint-below-
-- any-prefixpoint property (Knaster–Tarski / soundness of derivations w.r.t. models). From it,
-- the REFUTATION soundness for any derivation depth:
--
--   no_valid_excluded : ∀ d, band (derivValid m d) (bnot (holds m (derivHead d))) = false
--
-- — a model that EXCLUDES a relation admits NO valid derivation of it. Instantiated at `error`:
-- a satisfying model that excludes error proves error UNDERIVABLE at any depth ⇒ the program is
-- safe even in the presence of loops. That is `realPanics ⊆ models` with no depth bound.
--
-- HOW THE BLOCK WAS CLEARED: the recursion over the derivation tree was previously blocked —
-- clean's `induction` tactic panics in close_fvars and the recursive-def dependent `match`
-- mis-tracks the matched variable's motive. Both are elaborator-layer bugs. Applying the KERNEL
-- RECURSOR `@Deriv.rec` directly as a term sidesteps the elaborator entirely: the result is a
-- closed, kernel-type-checked proof term by construction — no FVar-closing, no motive inference.
-- (The induction-tactic bug remains a separate clean fix; this gives a SOUND path to the proof
-- now, with zero risk to the elaborator's trusted base.)
-- Kernel-checked through clean; covered by the ouroboros gate.

def bnot (a : Bool) : Bool := match a with | true => false | false => true
def bor (a : Bool) (b : Bool) : Bool := match a with | true => true | false => b
def band (a : Bool) (b : Bool) : Bool := match a with | true => b | false => false
def bimplies (a : Bool) (b : Bool) : Bool := bor (bnot a) b

-- Modus ponens at the equation level (`simp only [hp,…]` rewrites P := true, then `bimplies true
-- Q` reduces to Q). Used by the one-step lemma below.
theorem mp_eq (P Q : Bool) (h : bimplies P Q = true) (hp : P = true) : Q = true := by
  simp only [hp, bimplies, bnot, bor] at h
  exact h

-- ── The encoded system, as in chc_vc_datatype.lean: typed relations, a relation interpretation
-- (Model), rules (RuleBody.relation + constraint ⇒ head), and rule satisfaction. ──────────────
inductive Rel where
  | r0 : Rel
  | r1 : Rel
  | err : Rel
inductive Model where
  | mk : Bool -> Bool -> Bool -> Model
def holds (m : Model) (r : Rel) : Bool :=
  match m with
  | Model.mk a b e =>
    match r with
    | Rel.r0 => a
    | Rel.r1 => b
    | Rel.err => e
inductive Rule where
  | fact : Bool -> Rel -> Rule
  | step : Rel -> Bool -> Rel -> Rule
def ruleHead : Rule -> Rel
  | Rule.fact _ h => h
  | Rule.step _ _ h => h
def ruleBodyHolds (m : Model) (r : Rule) : Bool :=
  match r with
  | Rule.fact c _ => c
  | Rule.step b c _ => band c (holds m b)
def satisfies (m : Model) (r : Rule) : Bool :=
  bimplies (ruleBodyHolds m r) (holds m (ruleHead r))

-- ── A DERIVATION TREE of arbitrary depth. `dfact c h` applies a fact rule; `dstep c h sub`
-- applies a transition rule whose body relation is the sub-derivation's head. `derivValid m d`
-- holds iff every applied rule is satisfied by m and every constraint fires — a valid derivation
-- of `derivHead d` using only m-satisfied rules. Unbounded depth ⇒ this models loops. ──────────
inductive Deriv where
  | dfact : Bool -> Rel -> Deriv
  | dstep : Bool -> Rel -> Deriv -> Deriv
def derivHead : Deriv -> Rel
  | Deriv.dfact _ h => h
  | Deriv.dstep _ h _ => h
def derivValid (m : Model) (d : Deriv) : Bool :=
  match d with
  | Deriv.dfact c h => band c (satisfies m (Rule.fact c h))
  | Deriv.dstep c h sub =>
      band (derivValid m sub) (band c (satisfies m (Rule.step (derivHead sub) c h)))

-- A fact's head holds: validity `c ∧ (c ⟹ head)` forces head.
theorem taut_fact (c X : Bool) : bimplies (band c (bimplies c X)) X = true := by
  cases c with
  | true => cases X with | true => rfl | false => rfl
  | false => cases X with | true => rfl | false => rfl

-- The boolean content of one step, GIVEN the sub-derivation's prefixpoint (DV ⟹ HS).
theorem taut_step (DV HS HH c : Bool) :
    bimplies (bimplies DV HS) (bimplies (band DV (band c (bimplies (band c HS) HH))) HH) = true := by
  cases DV with
  | true => cases HS with
    | true => cases HH with
      | true => cases c with | true => rfl | false => rfl
      | false => cases c with | true => rfl | false => rfl
    | false => cases HH with
      | true => cases c with | true => rfl | false => rfl
      | false => cases c with | true => rfl | false => rfl
  | false => cases HS with
    | true => cases HH with
      | true => cases c with | true => rfl | false => rfl
      | false => cases c with | true => rfl | false => rfl
    | false => cases HH with
      | true => cases c with | true => rfl | false => rfl
      | false => cases c with | true => rfl | false => rfl

-- THE INDUCTIVE STEP (the dstep minor premise of the recursor): given the IH `DV ⟹ HS`, a
-- satisfied transition propagates truth to its head.
theorem dstep_sound (DV HS HH c : Bool) (ih : bimplies DV HS = true) :
    bimplies (band DV (band c (bimplies (band c HS) HH))) HH = true :=
  mp_eq (bimplies DV HS)
        (bimplies (band DV (band c (bimplies (band c HS) HH))) HH)
        (taut_step DV HS HH c) ih

-- ── THE UNBOUNDED PREFIXPOINT, via the KERNEL RECURSOR applied as a term. The minor premises are
-- the fact case (taut_fact) and the step case (dstep_sound fed the recursor-supplied IH). Closed
-- and kernel-checked by construction — no induction tactic, no equation compiler. ──────────────
def deriv_prefixpoint (m : Model) (d : Deriv) :
    bimplies (derivValid m d) (holds m (derivHead d)) = true :=
  @Deriv.rec.{0}
    (fun d => bimplies (derivValid m d) (holds m (derivHead d)) = true)
    (fun c h => taut_fact c (holds m h))
    (fun c h sub ih => dstep_sound (derivValid m sub) (holds m (derivHead sub)) (holds m h) c ih)
    d

-- De Morgan (all-concrete, no absurd branch): band DV (bnot H) = bnot (bimplies DV H).
theorem demorgan (DV H : Bool) : band DV (bnot H) = bnot (bimplies DV H) := by
  cases DV with
  | true => cases H with | true => rfl | false => rfl
  | false => cases H with | true => rfl | false => rfl

-- ── THE REFUTATION SOUNDNESS, for ANY derivation depth: a model cannot both make a derivation
-- valid and exclude its head — `band (valid) (head-excluded) = false`. Instantiated at `error`:
-- a satisfying model that excludes error admits no valid derivation of error at ANY depth ⇒
-- error underivable ⇒ safe (loops included). ───────────────────────────────────────────────────
theorem no_valid_excluded (m : Model) (d : Deriv) :
    band (derivValid m d) (bnot (holds m (derivHead d))) = false :=
  Eq.trans (demorgan (derivValid m d) (holds m (derivHead d)))
           (congrArg bnot (deriv_prefixpoint m d))

-- ── Concrete: an arbitrary-depth error derivation entry(r0) ⊳ r0→r1 ⊳ r1→error. ────────────────
def errDeriv : Deriv :=
  Deriv.dstep true Rel.err (Deriv.dstep true Rel.r1 (Deriv.dfact true Rel.r0))
theorem errDeriv_head : derivHead errDeriv = Rel.err := rfl
-- A valid error-derivation forces error true in the model (prefixpoint at err).
theorem errDeriv_forces_error (m : Model) :
    bimplies (derivValid m errDeriv) (holds m Rel.err) = true :=
  deriv_prefixpoint m errDeriv
-- The certificate refutes it: a model that EXCLUDES error makes the (reachable) error derivation
-- INVALID — the panic cannot be validly derived under an error-excluding interpretation.
def certModel : Model := Model.mk true true false      -- r0,r1 reachable, error EXCLUDED
theorem certModel_excludes_error : holds certModel Rel.err = false := rfl
theorem certModel_invalidates_errDeriv : derivValid certModel errDeriv = false := rfl
