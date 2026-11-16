/-
  Copyright 2026 Andrew Yates
  SPDX-License-Identifier: Apache-2.0

  # AY pseudo-Boolean UNSAT verdict — cutting-planes / RUP refutation soundness

  UNSAT is the OTHER unguarded verdict surface of the AY PB solver: unlike a SAT
  incumbent, an UNSAT verdict has NO model for the Verified Incumbent Gate to
  re-check at runtime. AY emits UNSAT through cutting-planes reasoning and a
  DRAT/LRAT certificate checked by the Rust `crates/ay-lrat-check` checker
  (`verify_proof`). This file gives the kernel-verified soundness backbone for
  that verdict, in two layers, both verified to axiom closure ⊆
  {propext, Quot.sound, Classical.choice}:

  1. **PB-native cutting-planes refutation** (`AyPb` namespace).  Over the SAME
     ℤ/Bool PB model that `ay_pb_optimum_gate.lean` mirrors onto the real Rust
     objects, we build the cutting-planes inference rules — axiom introduction,
     linear addition of two `≥` rows, monotone weakening — and prove the keystone
     soundness theorem: if from a constraint DB `D` one can derive a lower bound
     `lo ≤ L` and an upper bound `L ≤ hi` on the same linear form `L` with
     `hi < lo`, then `D` is UNSATISFIABLE (no Boolean assignment satisfies every
     row). The "ending in the empty clause `0 ≥ 1`" case is the corollary
     `pb_unsat_of_empty_clause`. A concrete 1-variable instance
     (`pb_example_db`) is refuted end-to-end (`pb_example_unsat`), with `rfl`
     non-vacuity controls proving the model actually computes.

  2. **CNF → PB encoding bridge** (`AyPbBridge` namespace).  AY's actual UNSAT
     certificate is a CNF DRAT/LRAT proof. The companion file
     `proofs/lrat_checker.lean` already proves `checkProof_sound : checkProof F
     prf = true → Unsat F` (CNF unsatisfiability from a verified LRAT cert). Here
     we close the last link: given an encoding-soundness witness — every
     PB-feasible assignment maps to a model of the CNF encoding `F` — CNF
     unsatisfiability of `F` entails UNSAT of the original PB row-set `D`
     (`pb_unsat_of_cnf_unsat`). Composed with `checkProof_sound`, a verified LRAT
     refutation of the encoding CNF discharges the PB UNSAT verdict.

  ## Bridge to AY's real types (crates/ay-pb/src) — see also ay_pb_optimum_gate.lean

  | This file        | AY Rust object (file:symbol)                                |
  |------------------|-------------------------------------------------------------|
  | `PbLit`          | `types.rs::PbLit { var: u32, negated: bool }`               |
  | `PbTerm`         | `types.rs::PbTerm { coeff: i128, lits: Vec<PbLit> }`        |
  | `PbRel`          | `types.rs::PbRel { Ge, Eq }`                                |
  | `PbConstraint`   | `types.rs::PbConstraint { terms, rel, rhs: i128 }`         |
  | `litVal`         | `solver.rs::eval_lit` (negation flips the assignment bit)   |
  | `termActive`     | `solver.rs::eval_term` (AND of a term's literals)           |
  | `evalTerms`      | `solver.rs::eval_terms` (Σ coeff over active terms, i128)   |
  | `evalConstraint` | `solver.rs:15 eval_constraint` (Ge: lhs≥rhs, Eq: lhs=rhs)   |
  | `verifyAll`      | `eval.rs:11 verify_all_constraints` (the VIG oracle)        |
  | `PbUnsat`        | the UNSAT verdict: no `assignment: &[bool]` satisfies `D`   |

  i128 fidelity: AY coefficients/values are signed `i128`; here they are `ℤ`
  (`Int`), the exact mathematical model of two's-complement `i128` in the
  non-overflowing regime AY's exact evaluators operate in. Assignments are
  modelled as total `Nat → Bool`; AY indexes a finite `&[bool]` 1-based with
  out-of-range defaulting to `false` (`eval_lit`'s `var.checked_sub(1)`), a
  faithful relabelling that the total-function model abstracts. The load-bearing
  arithmetic — transitivity of `≤`, strict/non-strict order interaction, and
  additive monotonicity — is discharged by the constructive prelude theorems
  `Int.le_trans`, `Int.lt_of_le_of_lt`, `Int.lt_irrefl`, `Int.add_le_add_left`,
  `Int.add_le_add_right` (empty domain-axiom closure).
-/

set_option autoImplicit false

namespace AyPb

/-! ## The PB model (mirrors `ay_pb::{types,solver,eval}`) -/

/-- A pseudo-Boolean literal. Mirrors `PbLit { var: u32, negated: bool }`. -/
structure PbLit where
  var : Nat
  negated : Bool

/-- Literal value under a total assignment. Mirrors `solver.rs::eval_lit`
    (negation flips the bit). -/
def litVal (a : Nat → Bool) (l : PbLit) : Bool :=
  match l.negated with
  | true  => Bool.not (a l.var)
  | false => a l.var

/-- A term: coefficient × conjunction of literals.
    Mirrors `PbTerm { coeff: i128, lits: Vec<PbLit> }`. -/
structure PbTerm where
  coeff : Int
  lits  : List PbLit

/-- A term is active iff all its literals evaluate to true. Mirrors `eval_term`. -/
def termActive (a : Nat → Bool) (ls : List PbLit) : Bool :=
  match ls with
  | []      => true
  | l :: ls =>
    match litVal a l with
    | true  => termActive a ls
    | false => false

/-- LHS value: Σ coefficients of the active terms. Mirrors `eval_terms`. -/
def evalTerms (a : Nat → Bool) (ts : List PbTerm) : Int :=
  match ts with
  | []      => 0
  | t :: ts =>
    match termActive a t.lits with
    | true  => t.coeff + evalTerms a ts
    | false => evalTerms a ts

/-- Relational operator. Mirrors `PbRel { Ge, Eq }`. -/
inductive PbRel where
  | ge
  | eq

/-- A single constraint `Σ terms rel rhs`. Mirrors `PbConstraint`. -/
structure PbConstraint where
  terms : List PbTerm
  rel   : PbRel
  rhs   : Int

/-- Evaluate a constraint, exactly as `eval_constraint`: `Ge => lhs ≥ rhs`,
    `Eq => lhs = rhs`.

    HISTORICAL NOTE (Clean bug now FIXED): a `match … with | PbRel.ge => … |
    PbRel.eq => …` on a *user-defined* enum with QUALIFIED constructor patterns used
    to iota-reduce to the first listed arm regardless of the scrutinee (the elaborator
    failed to resolve the namespaced pattern and silently fell back to a catch-all that
    mis-bound every minor onto the first arm). That is fixed in `clean-elab`
    (`resolve_ctor_name` now suffix-matches qualified patterns against the inductive's
    own constructor list), so the natural `match` below now compiles to the correct
    `PbRel.casesOn` dispatch and is kernel-sound. -/
def evalConstraint (a : Nat → Bool) (c : PbConstraint) : Bool :=
  match c.rel with
  | PbRel.ge => decide (Int.le c.rhs (evalTerms a c.terms))
  | PbRel.eq => decide (evalTerms a c.terms = c.rhs)

/-- The Verified Incumbent Gate oracle: every row holds. Mirrors
    `verify_all_constraints`. -/
def verifyAll (a : Nat → Bool) (cs : List PbConstraint) : Bool :=
  match cs with
  | []      => true
  | c :: cs =>
    match evalConstraint a c with
    | true  => verifyAll a cs
    | false => false

/-- **UNSAT verdict**: no total Boolean assignment satisfies every row of `D`.
    This is exactly the unguarded surface — there is no witness model for the
    VIG to re-check. -/
def PbUnsat (D : List PbConstraint) : Prop :=
  ∀ a : Nat → Bool, verifyAll a D = true → False

/-! ## Reasoning primitives -/

/-- `decide`-elimination (Clean lacks `of_decide_eq_true`; built from the
    `Decidable` recursor). -/
theorem of_decide {p : Prop} (inst : Decidable p) (h : @decide p inst = true) : p :=
  @Decidable.casesOn p (fun (d : Decidable p) => (@Eq Bool (@decide p d) true) → p)
    inst
    (fun _ hh => Bool.noConfusion hh)
    (fun hp _ => hp)
    h

/-- Recover `c.rhs ≤ lhs` from a satisfied `Ge` decision. -/
theorem int_le_of_decide (x y : Int) (h : decide (Int.le x y) = true) : Int.le x y :=
  of_decide (Int.decLe x y) h

/-- Recover `Σ ts = r` from a satisfied `Eq` decision (instance inferred from the
    proof; `decide`-elimination only cases on the `Decidable` instance and never
    requires it to reduce). -/
theorem int_eq_of_decide (e r : Int) (h : decide (e = r) = true) : e = r :=
  of_decide _ h

/-! ## `evalTerms` is additive over list concatenation (the cutting-planes sum)

These are proved in pure term mode via the kernel recursors: Clean's `rw`/`simp
only [evalTerms]`/`show`/`cases` tactics currently mis-handle the nested
`match`-on-`Bool` inside a recursive `def` (they either fail to find the global
rewrite or mis-elaborate the motive), so the cons/append lemmas use explicit
`@Bool.rec` / `@List.rec` with the reduced match form as motive — the idiom the
companion `lrat_checker.lean` documents. -/

theorem evalTerms_nil (a : Nat → Bool) : evalTerms a [] = 0 := rfl

/-- The nil case of `evalTerms_append`, with the exact `@List.rec` motive type at
    `[]` so the certificate replayer (whose defeq is stricter than the checker)
    matches it without reducing `[] ++ ys`. -/
theorem evalTerms_append_nil (a : Nat → Bool) (ys : List PbTerm) :
    evalTerms a (([] : List PbTerm) ++ ys) = evalTerms a ([] : List PbTerm) + evalTerms a ys :=
  (Int.zero_add (evalTerms a ys)).symm

/-- The cons step of `evalTerms_append` (the `Bool` split, term mode), with the
    exact `@List.rec` motive type at `t :: ts`. -/
theorem evalTerms_append_step (a : Nat → Bool) (t : PbTerm) (ts ys : List PbTerm)
    (ih : evalTerms a (ts ++ ys) = evalTerms a ts + evalTerms a ys) :
    evalTerms a ((t :: ts) ++ ys) = evalTerms a (t :: ts) + evalTerms a ys :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
        | true  => t.coeff + evalTerms a (ts ++ ys)
        | false => evalTerms a (ts ++ ys))
      = (match b with
        | true  => t.coeff + evalTerms a ts
        | false => evalTerms a ts) + evalTerms a ys)
    ih
    (Eq.trans
      (congrArg (fun z => t.coeff + z) ih)
      (Int.add_assoc t.coeff (evalTerms a ts) (evalTerms a ys)).symm)
    (termActive a t.lits)

/-- **Cutting-planes addition is sound on the LHS**: the value of the appended
    term lists is the sum of the values. -/
theorem evalTerms_append (a : Nat → Bool) (xs ys : List PbTerm) :
    evalTerms a (xs ++ ys) = evalTerms a xs + evalTerms a ys :=
  @List.rec PbTerm
    (fun xs => evalTerms a (xs ++ ys) = evalTerms a xs + evalTerms a ys)
    (evalTerms_append_nil a ys)
    (fun t ts ih => evalTerms_append_step a t ts ys ih)
    xs

/-- Additive monotonicity of `≤` on both arguments (from the prelude one-sided
    lemmas + transitivity). -/
theorem add_le_add (r1 r2 L1 L2 : Int) (h1 : Int.le r1 L1) (h2 : Int.le r2 L2) :
    Int.le (r1 + r2) (L1 + L2) :=
  Int.le_trans (r1 + r2) (L1 + r2) (L1 + L2)
    (Int.add_le_add_right r1 L1 h1 r2)
    (Int.add_le_add_left r2 L2 h2 L1)

/-! ## The cutting-planes / RUP refutation calculus

A *derived lower bound* `ImpliedGe D ts lo` says: every assignment satisfying
all of `D` makes the linear form `Σ ts` at least `lo`. An *upper bound*
`ImpliedLe D ts hi` is dual. These are exactly the semantic facts a
cutting-planes proof accumulates; the inference rules below produce them. -/

/-- `D` entails the lower bound `lo ≤ Σ ts`. -/
def ImpliedGe (D : List PbConstraint) (ts : List PbTerm) (lo : Int) : Prop :=
  ∀ a : Nat → Bool, verifyAll a D = true → Int.le lo (evalTerms a ts)

/-- `D` entails the upper bound `Σ ts ≤ hi`. -/
def ImpliedLe (D : List PbConstraint) (ts : List PbTerm) (hi : Int) : Prop :=
  ∀ a : Nat → Bool, verifyAll a D = true → Int.le (evalTerms a ts) hi

/-- Head extraction for the VIG oracle: if every row of `c :: cs` holds then `c`
    holds. -/
theorem verifyAll_cons_head (a : Nat → Bool) (c : PbConstraint) (cs : List PbConstraint)
    (h : verifyAll a (c :: cs) = true) : evalConstraint a c = true :=
  @Bool.rec
    (fun x : Bool => (@Eq Bool (match x with | true => verifyAll a cs | false => false) true) → (x = true))
    (fun hh => Bool.noConfusion hh)
    (fun _ => rfl)
    (evalConstraint a c) h

/-- Tail extraction for the VIG oracle. -/
theorem verifyAll_cons_tail (a : Nat → Bool) (c : PbConstraint) (cs : List PbConstraint)
    (h : verifyAll a (c :: cs) = true) : verifyAll a cs = true :=
  @Bool.rec
    (fun x : Bool => (@Eq Bool (match x with | true => verifyAll a cs | false => false) true) → (verifyAll a cs = true))
    (fun hh => Bool.noConfusion hh)
    (fun hh => hh)
    (evalConstraint a c) h

/-- **Rule (addition).** Adding a lower bound `lo ≤ Σ xs` and a lower bound
    `lo' ≤ Σ ys` yields the lower bound `lo + lo' ≤ Σ (xs ++ ys)` — the linear
    combination step of cutting planes. -/
theorem impliedGe_add (D : List PbConstraint) (xs ys : List PbTerm) (lo lo' : Int)
    (hx : ImpliedGe D xs lo) (hy : ImpliedGe D ys lo') :
    ImpliedGe D (xs ++ ys) (lo + lo') :=
  fun a va =>
    Eq.mpr
      (congrArg (Int.le (lo + lo')) (evalTerms_append a xs ys))
      (add_le_add lo lo' (evalTerms a xs) (evalTerms a ys) (hx a va) (hy a va))

/-- **Rule (addition, dual).** Sum of two upper bounds is an upper bound of the
    appended form. -/
theorem impliedLe_add (D : List PbConstraint) (xs ys : List PbTerm) (hi hi' : Int)
    (hx : ImpliedLe D xs hi) (hy : ImpliedLe D ys hi') :
    ImpliedLe D (xs ++ ys) (hi + hi') :=
  fun a va =>
    Eq.mpr
      (congrArg (fun z => Int.le z (hi + hi')) (evalTerms_append a xs ys))
      (add_le_add (evalTerms a xs) (evalTerms a ys) hi hi' (hx a va) (hy a va))

/-- **Rule (weaken).** A lower bound may be relaxed downward. -/
theorem impliedGe_weaken (D : List PbConstraint) (ts : List PbTerm) (lo lo' : Int)
    (hle : Int.le lo' lo) (h : ImpliedGe D ts lo) : ImpliedGe D ts lo' :=
  fun a va => Int.le_trans lo' lo (evalTerms a ts) hle (h a va)

/-- `0 < 1` over `ℤ`, as a named lemma (the certificate replayer matches a
    named constant by type exactly, whereas an inline `Int.le_refl 1` would need
    the replayer to unfold `Int.lt 0 1 ≡ Int.le (0+1) 1 ≡ Int.le 1 1`). -/
theorem int_lt_0_1 : Int.lt 0 1 := Int.le_refl 1

/-! ## The UNSAT keystone -/

/-- **Cutting-planes refutation soundness.** If `D` entails a lower bound `lo`
    and an upper bound `hi` on the same linear form `ts`, and `hi < lo`, then no
    assignment satisfies `D`: `D` is UNSAT. This is the soundness obligation
    behind every PB UNSAT verdict AY emits via cutting planes. Load-bearing
    arithmetic: `lo ≤ Σ ts ≤ hi` forces `lo ≤ hi` (transitivity), contradicting
    `hi < lo` (`lt_of_le_of_lt` + `lt_irrefl`). -/
theorem pb_unsat_of_contradictory_bounds
    (D : List PbConstraint) (ts : List PbTerm) (lo hi : Int)
    (hLo : ImpliedGe D ts lo) (hHi : ImpliedLe D ts hi) (hGap : Int.lt hi lo) :
    PbUnsat D :=
  fun a va =>
    Int.lt_irrefl lo
      (Int.lt_of_le_of_lt lo hi lo
        (Int.le_trans lo (evalTerms a ts) hi (hLo a va) (hHi a va)) hGap)

/-- **Empty-clause corollary.** A cutting-planes derivation ending in the empty
    clause `0 ≥ 1` — i.e. `D` entails `1 ≤ Σ [] = 0` — refutes `D`. This is the
    PB image of "a RUP derivation ending in the empty clause entails UNSAT". -/
theorem pb_unsat_of_empty_clause
    (D : List PbConstraint) (hEmpty : ImpliedGe D [] 1) : PbUnsat D :=
  pb_unsat_of_contradictory_bounds D [] 1 0
    hEmpty
    (fun _ _ => Int.le_refl 0)
    int_lt_0_1

/-! ## Non-vacuity: a concrete UNSAT instance refuted end-to-end

The DB asserts both `x ≥ 1` (variable 0 must be true) and `x = 0` (it must be
false). These rows are contradictory; `pb_example_unsat` derives `PbUnsat`. -/

def pb_example_x : PbLit := { var := 0, negated := false }

/-- The single linear form `1·x`. -/
def pb_example_terms : List PbTerm := [{ coeff := 1, lits := [pb_example_x] }]

/-- Row `1·x ≥ 1`. -/
def pb_example_c0 : PbConstraint := { terms := pb_example_terms, rel := PbRel.ge, rhs := 1 }

/-- Row `1·x = 0`. -/
def pb_example_c1 : PbConstraint := { terms := pb_example_terms, rel := PbRel.eq, rhs := 0 }

def pb_example_db : List PbConstraint := [pb_example_c0, pb_example_c1]

/-- `c0` gives the lower bound `1 ≤ x`. -/
theorem pb_example_lo : ImpliedGe pb_example_db pb_example_terms 1 :=
  fun a va =>
    int_le_of_decide 1 (evalTerms a pb_example_terms)
      (verifyAll_cons_head a pb_example_c0 [pb_example_c1] va)

/-- `c1` gives the upper bound `x ≤ 0`. -/
theorem pb_example_hi : ImpliedLe pb_example_db pb_example_terms 0 :=
  fun a va =>
    Eq.mpr
      (congrArg (fun z => Int.le z 0)
        (int_eq_of_decide (evalTerms a pb_example_terms) 0
          (verifyAll_cons_head a pb_example_c1 []
            (verifyAll_cons_tail a pb_example_c0 [pb_example_c1] va))))
      (Int.le_refl 0)

/-- **The worked instance is UNSAT** (kernel-verified, end-to-end). -/
theorem pb_example_unsat : PbUnsat pb_example_db :=
  pb_unsat_of_contradictory_bounds pb_example_db pb_example_terms 1 0
    pb_example_lo pb_example_hi int_lt_0_1

/-! ### Non-vacuity controls — the model genuinely computes (not vacuous).

The objective form `1·x` evaluates to genuinely different values under the two
assignments, and the `Ge` row `c0` distinguishes them: the UNSAT verdict is a
real fact about a computing model, not a trivially-false gate. (The `Eq` row's
decision is satisfiability-checked via `int_eq_of_decide` above; Clean's kernel
does not iota-reduce `decide (·=·)` on `Int` through a definition's instance, so
the controls exercise the `Ge` / `evalTerms` paths, which do reduce.) -/

/-- `1·x` is `1` when `x = true`. -/
theorem pb_ctrl_terms_true  : evalTerms (fun _ => true)  pb_example_terms = 1 := rfl
/-- `1·x` is `0` when `x = false` — c1 (=0) holds here but c0 (≥1) then fails. -/
theorem pb_ctrl_terms_false : evalTerms (fun _ => false) pb_example_terms = 0 := rfl
/-- With `x = true`, `c0` (x ≥ 1) is satisfied. -/
theorem pb_ctrl_c0_true  : evalConstraint (fun _ => true)  pb_example_c0 = true  := rfl
/-- With `x = false`, `c0` (x ≥ 1) is violated, so the whole DB fails (no all-false model). -/
theorem pb_ctrl_c0_false : evalConstraint (fun _ => false) pb_example_c0 = false := rfl
/-- The all-false assignment does not satisfy the DB (c0 fails) — verified by reduction. -/
theorem pb_ctrl_db_false_false : verifyAll (fun _ => false) pb_example_db = false := rfl

end AyPb

/-! # CNF → PB encoding bridge

This is the second link of the UNSAT verdict: AY actually proves UNSAT by
emitting a CNF DRAT/LRAT certificate. `proofs/lrat_checker.lean` proves
`checkProof_sound : checkProof F prf = true → Unsat F`. The theorem below lifts
that CNF-level `Unsat` up to the PB row-set, given an encoding-soundness witness. -/

namespace AyPbBridge

open AyPb

/-- A CNF literal over the same variable space. -/
structure CnfLit where
  var : Nat
  negated : Bool

def satCnfLit (a : Nat → Bool) (l : CnfLit) : Bool :=
  match l.negated with
  | true  => Bool.not (a l.var)
  | false => a l.var

/-- A clause is satisfied iff some literal is. -/
def satCnfClause (a : Nat → Bool) (cl : List CnfLit) : Bool :=
  match cl with
  | []      => false
  | l :: ls =>
    match satCnfLit a l with
    | true  => true
    | false => satCnfClause a ls

/-- A formula (CNF) is satisfied iff every clause is. -/
def satCnfFormula (a : Nat → Bool) (f : List (List CnfLit)) : Bool :=
  match f with
  | []      => true
  | c :: cs =>
    match satCnfClause a c with
    | true  => satCnfFormula a cs
    | false => false

/-- `a` is a model of the CNF `f`. Retained as a readable `Prop` abstraction.

    HISTORICAL NOTE (Clean bug now FIXED): a hypothesis of shape
    `∀ a, P a → g a = true` used to mis-parse — the parser bound `→` tighter than
    `=`, reading `P a → g a = true` as `(P a → g a) = true` and reporting "expected
    valid type, got Sort Bool". That precedence bug is fixed in `clean-parser` (an
    arrow's codomain now parses at full expression precedence, so `=` binds tighter
    than `→` as in Lean), so the bare-`Eq` codomain elaborates directly now; the
    `def` wrapper below is kept only for readability. -/
def CnfModels (a : Nat → Bool) (f : List (List CnfLit)) : Prop :=
  satCnfFormula a f = true

/-- CNF unsatisfiability — exactly what `lrat_checker.lean`'s `checkProof_sound`
    discharges from a verified LRAT certificate (`Unsat F`). -/
def CnfUnsat (f : List (List CnfLit)) : Prop :=
  ∀ a : Nat → Bool, CnfModels a f → False

/-- **The encoding bridge.** Let `enc` map each PB assignment to a CNF
    assignment, with the *encoding-soundness* property that every `D`-feasible
    PB assignment is mapped to a model of the CNF encoding `F` (`hsound`). Then
    CNF-unsatisfiability of `F` entails UNSAT of the PB row-set `D`.

    Composition: take `F` = AY's Tseitin/cardinality CNF encoding of `D`, obtain
    `CnfUnsat F` from `lrat_checker.checkProof_sound` applied to AY's verified
    DRAT/LRAT certificate, and conclude `PbUnsat D`. -/
theorem pb_unsat_of_cnf_unsat
    (D : List PbConstraint) (F : List (List CnfLit))
    (enc : (Nat → Bool) → (Nat → Bool))
    (hsound : ∀ a : Nat → Bool, verifyAll a D = true → CnfModels (enc a) F)
    (hcnf : CnfUnsat F) :
    PbUnsat D :=
  fun a va => hcnf (enc a) (hsound a va)

/-! ### Bridge non-vacuity controls. -/

/-- A genuinely unsatisfiable CNF: `(x) ∧ (¬x)`. -/
def bridge_ctrl_cnf : List (List CnfLit) :=
  [[({ var := 0, negated := false } : CnfLit)], [({ var := 0, negated := true } : CnfLit)]]

/-- `x = true` satisfies the first clause but not the second. -/
theorem bridge_ctrl_true  : satCnfFormula (fun _ => true)  bridge_ctrl_cnf = false := rfl
/-- `x = false` fails the first clause. -/
theorem bridge_ctrl_false : satCnfFormula (fun _ => false) bridge_ctrl_cnf = false := rfl

end AyPbBridge


/-! # Closing the two manual links to real Rust (gaps (a) and (b))

The keystone `AyPb.pb_unsat_of_contradictory_bounds` and the bridge
`AyPbBridge.pb_unsat_of_cnf_unsat` are kernel-verified over the ℤ / total-`Nat→Bool`
model. Two correspondences to the ACTUAL `crates/ay-pb` Rust were previously stated
only in prose (the header's "i128 fidelity" / "1-based slice" paragraphs):

  (a) AY accumulates the constraint LHS in `i128` (`solver.rs::eval_terms`,
      `eval_terms_checked`), not unbounded ℤ; soundness holds in the
      *non-overflowing regime* where `i128::checked_add` never returns `Overflow`.

  (b) AY evaluates against a finite `&[bool]` slice indexed 1-based with
      out-of-range defaulting to `false` (`solver.rs::eval_lit`'s
      `var.checked_sub(1) … assignment.get(index) … unwrap_or(false)`), not a total
      `Nat → Bool`.

This section discharges BOTH as kernel-checked Clean lemmas, composing them into a
single end-to-end theorem `real_unsat_of_pb_unsat`: if the ℤ / total model says `D`
is UNSAT, then NO finite Boolean slice, evaluated with `i128` checked arithmetic in
the non-overflow regime, satisfies `D`. No prose hand-waving remains between the
real Rust evaluator and the kernel UNSAT theorem.

Engineering note: every recursor motive below is kept *match-free* (case bodies are
factored into named `def`s — `boolGuard`, `restGuard`, `addActiveChecked`,
`lhsGuard`, `boolStep`, `stepVerify`, `verifyStep`). A `match` written directly
inside a `@Bool.rec` / `@Option.rec` motive currently trips Clean's universe
inference; the named-def idiom both dodges that and keeps the kernel's iota
reduction trivially aligned with the definitions. -/

namespace AyPbReal

open AyPb

/-! ## Small Option projections (Clean exposes no `Option.noConfusion`/`.inj`;
    we go through total projections with `congrArg`, as the file does for `Bool`). -/

def optVal0    (o : Option Int)  : Int  := match o with | some x => x | none => 0
def optIsSomeI (o : Option Int)  : Bool := match o with | some _ => true | none => false
def optValB    (o : Option Bool) : Bool := match o with | some x => x | none => false
def optIsSomeB (o : Option Bool) : Bool := match o with | some _ => true | none => false

/-! ## Gap (b): the real `&[bool]` slice vs the total `Nat → Bool` model -/

/-- `assignment.get index` on a 0-based `List Bool`, exactly `slice.get(i)`. -/
def sliceGet (s : List Bool) (i : Nat) : Option Bool :=
  match s with
  | []      => none
  | b :: bs =>
    match i with
    | 0          => some b
    | Nat.succ j => sliceGet bs j

/-- The value AY's `eval_lit` reads for variable `v`: `var.checked_sub(1)` is
    `None` for `v = 0` (→ `false`), else indexes `slice.get(v-1)`, out-of-range
    `→ false`. -/
def sliceVarVal (s : List Bool) (v : Nat) : Bool :=
  match v with
  | 0          => false
  | Nat.succ k =>
    match sliceGet s k with
    | some b => b
    | none   => false

/-- The total `Nat → Bool` assignment induced by a finite slice — the faithful
    relabelling of `eval_lit`'s 1-based indexing. -/
def totalOfSlice (s : List Bool) : Nat → Bool := fun v => sliceVarVal s v

/-- The literal value AY's `eval_lit` computes over the slice (negation flips the
    indexed bit). Mirrors `solver.rs::eval_lit` end to end. -/
def sliceLitVal (s : List Bool) (l : PbLit) : Bool :=
  match l.negated with
  | true  => Bool.not (sliceVarVal s l.var)
  | false => sliceVarVal s l.var

/-- **Gap (b), literal level.** AY's slice-based `eval_lit` agrees with the model's
    `litVal` on the induced total assignment. Definitional: `totalOfSlice s v`
    unfolds to `sliceVarVal s v`, and both sides are the same `match l.negated`. -/
theorem sliceLitVal_eq (s : List Bool) (l : PbLit) :
    sliceLitVal s l = litVal (totalOfSlice s) l := rfl

/-! ## Gap (a): exact `i128` accumulation vs unbounded ℤ -/

/-- `2^63`, a sub-`u64`-max literal the lexer accepts. -/
def twoPow63 : Int := 9223372036854775808
/-- `2^127 = (2^63)·(2^63)·2`, the magnitude of `i128::MIN` and one past `i128::MAX`. -/
def i128Pos : Int := twoPow63 * twoPow63 * 2

/-- `x` is representable as a two's-complement `i128`: `-2^127 ≤ x ≤ 2^127 - 1`. -/
def InI128 (x : Int) : Prop := And (Int.le (Int.neg i128Pos) x) (Int.le x (i128Pos - 1))

/-- Boolean `i128`-range test (the decidable image of `InI128`). -/
def inI128B (x : Int) : Bool :=
  Bool.and (decide (Int.le (Int.neg i128Pos) x)) (decide (Int.le x (i128Pos - 1)))

/-- A guarded option: `some p` when the flag holds, else `none`. Factors the body
    of `i128::checked_add` so the soundness motive stays match-free. -/
def boolGuard (c : Bool) (p : Int) : Option Int :=
  match c with | true => some p | false => none

/-- Faithful model of `i128::checked_add`: the exact integer sum when it fits the
    `i128` range, else `none` (Rust's `Overflow`). -/
def checkedAdd (x y : Int) : Option Int := boolGuard (inI128B (x + y)) (x + y)

/-- `boolGuard c p = some v → v = p`. The decidable-flag is treated as an opaque
    `Bool`, so this never forces the `i128` bound to reduce. -/
theorem boolGuard_some (c : Bool) (p v : Int) (h : boolGuard c p = some v) : v = p :=
  @Bool.rec (fun c => boolGuard c p = some v → v = p)
    (fun hh => Bool.noConfusion (congrArg optIsSomeI hh))
    (fun hh => (congrArg optVal0 hh).symm)
    c h

/-- **Gap (a), step.** When `checked_add` succeeds (no overflow), its value is the
    exact integer sum that the ℤ model uses. -/
theorem checkedAdd_some_eq (x y v : Int) (h : checkedAdd x y = some v) : v = x + y :=
  boolGuard_some (inI128B (x + y)) (x + y) v h

/-- The `some`-branch of the checked fold (factored to keep motives match-free). -/
def restGuard (coeff : Int) (o : Option Int) : Option Int :=
  match o with | some r => checkedAdd coeff r | none => none

/-- One fold step of `eval_terms_checked`: add the active term's coefficient to the
    running checked sum (skip when inactive). -/
def addActiveChecked (active : Bool) (coeff : Int) (rest : Option Int) : Option Int :=
  match active with | true => restGuard coeff rest | false => rest

/-- The model's plain (ℤ) fold step — definitionally the cons case of `evalTerms`. -/
def addPlain (active : Bool) (coeff sumTail : Int) : Int :=
  match active with | true => coeff + sumTail | false => sumTail

/-- The exact `i128` constraint-LHS evaluator: `eval_terms_checked`'s fold over the
    active terms with `checked_add`. `none` marks the partial sum leaving `i128`
    range (`ObjectiveEvalError::Overflow`). -/
def evalTermsChecked (a : Nat → Bool) (ts : List PbTerm) : Option Int :=
  match ts with
  | []      => some 0
  | t :: ts => addActiveChecked (termActive a t.lits) t.coeff (evalTermsChecked a ts)

/-- One fold step is sound: given the tail's value, a successful checked step
    yields the corresponding plain (ℤ) step value. -/
theorem addActiveChecked_eq
    (active : Bool) (coeff sumTail v : Int) (rest : Option Int)
    (ih : ∀ r : Int, rest = some r → r = sumTail)
    (h : addActiveChecked active coeff rest = some v) :
    v = addPlain active coeff sumTail :=
  @Bool.rec
    (fun active => addActiveChecked active coeff rest = some v → v = addPlain active coeff sumTail)
    (fun hh => ih v hh)
    (fun hh =>
      @Option.rec Int
        (fun o => rest = o → restGuard coeff o = some v → v = coeff + sumTail)
        (fun _ hh2 => Bool.noConfusion (congrArg optIsSomeI hh2))
        (fun r heq hh2 =>
          Eq.trans (checkedAdd_some_eq coeff r v hh2)
            (congrArg (fun z => coeff + z) (ih r heq)))
        rest rfl hh)
    active h

/-- **Gap (a), keystone.** In the non-overflow regime (the checked fold succeeds),
    AY's exact `i128` constraint LHS equals the unbounded-ℤ `evalTerms` the UNSAT
    theorem reasons about. -/
theorem evalTermsChecked_eq (a : Nat → Bool) (ts : List PbTerm) :
    ∀ v : Int, evalTermsChecked a ts = some v → v = evalTerms a ts :=
  @List.rec PbTerm
    (fun ts => ∀ v : Int, evalTermsChecked a ts = some v → v = evalTerms a ts)
    (fun v h => (congrArg optVal0 h).symm)
    (fun t ts ih => fun v h =>
      addActiveChecked_eq (termActive a t.lits) t.coeff (evalTerms a ts) v
        (evalTermsChecked a ts) ih h)
    ts

/-! ## Composing (a) ⊕ (b): the real slice + `i128` constraint / instance evaluator -/

/-- The `some`-branch of `realEvalConstraint` (factored; keeps motives match-free).
    The `Ge`/`Eq` comparison is on representable `i128` values, exactly the integer
    comparison the model uses. -/
def lhsGuard (c : PbConstraint) (o : Option Int) : Option Bool :=
  match o with
  | some lhs =>
    some (@PbRel.casesOn (fun _ => Bool) c.rel
      (decide (Int.le c.rhs lhs)) (decide (lhs = c.rhs)))
  | none => none

/-- AY's real `eval_constraint` on a slice: compute the LHS with checked `i128`
    accumulation over the slice-induced assignment; `none` = overflow. Mirrors
    `solver.rs:15`. -/
def realEvalConstraint (s : List Bool) (c : PbConstraint) : Option Bool :=
  lhsGuard c (evalTermsChecked (totalOfSlice s) c.terms)

/-- **Gaps (a)⊕(b), constraint level.** When the real slice+`i128` evaluator
    produces a verdict (no overflow), it equals the model's `evalConstraint` on the
    induced total assignment. -/
theorem realEvalConstraint_eq (s : List Bool) (c : PbConstraint) :
    ∀ b : Bool, realEvalConstraint s c = some b → b = evalConstraint (totalOfSlice s) c :=
  @Option.rec Int
    (fun o =>
      evalTermsChecked (totalOfSlice s) c.terms = o
      → ∀ b : Bool, lhsGuard c o = some b → b = evalConstraint (totalOfSlice s) c)
    (fun _ b h => Bool.noConfusion (congrArg optIsSomeB h))
    (fun lhs heq b h =>
      Eq.trans ((congrArg optValB h).symm)
        (congrArg
          (fun L => @PbRel.casesOn (fun _ => Bool) c.rel
            (decide (Int.le c.rhs L)) (decide (L = c.rhs)))
          (evalTermsChecked_eq (totalOfSlice s) c.terms lhs heq)))
    (evalTermsChecked (totalOfSlice s) c.terms)
    rfl

/-- `true`/`false` dispatch of one verified row (factored; keeps motives match-free). -/
def boolStep (tail : Option Bool) (b : Bool) : Option Bool :=
  match b with | true => tail | false => some false

/-- One instance-level step over an `Option Bool` row verdict. -/
def stepVerify (tail : Option Bool) (o : Option Bool) : Option Bool :=
  match o with | none => none | some b => boolStep tail b

/-- The model's plain instance step — definitionally the cons case of `verifyAll`. -/
/-- Introduce a `verifyAll` over a cons from its head/tail verdicts (the dual of
    the file's `verifyAll_cons_head`/`_tail`). Used to assemble the model verdict
    in `realVerifyAll_eq` without forcing the kernel to reduce `verifyAll (c::cs)`
    inside a deeply nested recursor minor. -/
theorem verifyAll_cons_intro (a : Nat → Bool) (c : PbConstraint) (cs : List PbConstraint)
    (hc : evalConstraint a c = true) (ht : verifyAll a cs = true) :
    verifyAll a (c :: cs) = true :=
  Eq.trans
    (congrArg (fun e : Bool => match e with | true => verifyAll a cs | false => false) hc)
    ht

/-- AY's real `verify_all_constraints` over a slice with `i128` arithmetic: every
    row must give `some true`; `none` (overflow) or any `some false` short-circuits.
    Mirrors `eval.rs:11`. -/
def realVerifyAll (s : List Bool) (cs : List PbConstraint) : Option Bool :=
  match cs with
  | []      => some true
  | c :: cs => stepVerify (realVerifyAll s cs) (realEvalConstraint s c)

/-- **Gaps (a)⊕(b), instance level.** If the real slice+`i128` evaluator accepts a
    slice (all rows `some true`, no overflow), the induced total assignment
    satisfies every row in the model. -/
theorem realVerifyAll_eq (s : List Bool) (cs : List PbConstraint) :
    realVerifyAll s cs = some true → verifyAll (totalOfSlice s) cs = true :=
  @List.rec PbConstraint
    (fun cs => realVerifyAll s cs = some true → verifyAll (totalOfSlice s) cs = true)
    (fun _ => rfl)
    (fun c cs ih => fun h =>
      @Option.rec Bool
        (fun o =>
          realEvalConstraint s c = o
          → stepVerify (realVerifyAll s cs) o = some true
          → verifyAll (totalOfSlice s) (c :: cs) = true)
        (fun _ h2 => Bool.noConfusion (congrArg optIsSomeB h2))
        (fun b =>
          @Bool.rec
            (fun b =>
              realEvalConstraint s c = some b
              → boolStep (realVerifyAll s cs) b = some true
              → verifyAll (totalOfSlice s) (c :: cs) = true)
            (fun _ h2 => Bool.noConfusion (congrArg optValB h2))
            (fun heq h2 =>
              verifyAll_cons_intro (totalOfSlice s) c cs
                (realEvalConstraint_eq s c true heq).symm (ih h2))
            b)
        (realEvalConstraint s c)
        rfl h)
    cs

/-- **The closed UNSAT chain.** No finite Boolean slice, evaluated with `i128`
    checked arithmetic in the non-overflow regime, satisfies `D` — provided the
    ℤ / total model proves `D` UNSAT. Both manual gaps are now kernel lemmas:
    the slice→total correspondence (b) and the i128→ℤ non-overflow
    correspondence (a). -/
def RealUnsat (D : List PbConstraint) : Prop :=
  ∀ s : List Bool, realVerifyAll s D = some true → False

theorem real_unsat_of_pb_unsat (D : List PbConstraint) (h : PbUnsat D) : RealUnsat D :=
  fun s hs => h (totalOfSlice s) (realVerifyAll_eq s D hs)

/-- The worked instance, lifted to the real evaluator. -/
theorem pb_example_real_unsat : RealUnsat pb_example_db :=
  real_unsat_of_pb_unsat pb_example_db pb_example_unsat

/-- Composed with the CNF bridge: a verified LRAT refutation of the encoding CNF
    discharges the *real* slice+`i128` UNSAT verdict. -/
theorem real_unsat_of_cnf_unsat
    (D : List PbConstraint) (F : List (List AyPbBridge.CnfLit))
    (enc : (Nat → Bool) → (Nat → Bool))
    (hsound : ∀ a : Nat → Bool, verifyAll a D = true → AyPbBridge.CnfModels (enc a) F)
    (hcnf : AyPbBridge.CnfUnsat F) :
    RealUnsat D :=
  real_unsat_of_pb_unsat D (AyPbBridge.pb_unsat_of_cnf_unsat D F enc hsound hcnf)

/-! ## Non-vacuity controls — the real model genuinely computes (not vacuous). -/

/-- Gap (b): variable 0 is the always-`false` sentinel (`checked_sub(1) = None`). -/
theorem ctrl_slice_var0 : totalOfSlice [false, true] 0 = false := rfl
/-- Gap (b): variable 1 reads slice element 0 (1-based indexing). -/
theorem ctrl_slice_var1 : totalOfSlice [false, true] 1 = false := rfl
/-- Gap (b): variable 2 reads slice element 1. -/
theorem ctrl_slice_var2 : totalOfSlice [false, true] 2 = true := rfl
/-- Gap (b): a variable past the slice end defaults to `false`. -/
theorem ctrl_slice_oob  : totalOfSlice [false, true] 9 = false := rfl

/-- Gap (a), small width (`bound = 8`, range `[-8,7]`) where the kernel can compute
    the bound (the real `2^127` bound is too large for `Int.le` to reduce quickly,
    a representation-perf matter orthogonal to the soundness lemmas, which never
    reduce it). The SAME definitional pattern as `checkedAdd` is exercised. -/
def demoInB (x : Int) : Bool :=
  Bool.and (decide (Int.le (Int.neg 8) x)) (decide (Int.le x 7))
def demoCheckedAdd (x y : Int) : Option Int := boolGuard (demoInB (x + y)) (x + y)
/-- In-range checked add returns the exact sum. -/
theorem ctrl_demo_ok : demoCheckedAdd 3 3 = some 6 := rfl
/-- Overflow (`5+5 = 10 > 7`) is rejected as `none` — the regime is real, not vacuous. -/
theorem ctrl_demo_overflow : demoCheckedAdd 5 5 = none := rfl
/-- Negative overflow (`-5 + -5 = -10 < -8`) is rejected. -/
theorem ctrl_demo_underflow : demoCheckedAdd (Int.neg 5) (Int.neg 5) = none := rfl
/-- The small-width `boolGuard_some` is non-vacuous: it really recovers the sum. -/
theorem ctrl_demo_some_eq : ∀ v : Int, demoCheckedAdd 3 3 = some v → v = 6 :=
  fun v h => boolGuard_some (demoInB (3 + 3)) (3 + 3) v h

/-- The all-false slice does not satisfy the worked DB under the real evaluator:
    row `c0` (`x ≥ 1`) fails (reduces through the `Ge`/`≤` paths; no big-bound add). -/
theorem ctrl_real_db_false : realVerifyAll [] pb_example_db = some false := rfl

end AyPbReal
