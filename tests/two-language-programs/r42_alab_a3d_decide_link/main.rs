//! THE "THIS MAGIC CONSTANT IS THE RIGHT ONE" SHAPE, on ALab code.
//!
//! ============================================================================
//! WHAT THIS ROW IS FOR
//! ============================================================================
//! AMENDED 2026-09-20, AFTER THE PIN MOVED. `decide_eq_decide` IS now in
//! Clean's prelude — this lane pushed it (`agents/decide-eq-decide-20260920`)
//! and `first-party/clean` was bumped to an integration branch carrying it the
//! same day. The measurement above was true when taken, against the pack
//! `379912412b1`, and is kept because it is what the row was written from.
//!
//! THE ROW DOES NOT CHANGE. Its island writes the `mpr` direction out as
//! `Decidable.rec` casework rather than citing the prelude lemma, deliberately:
//! Lean's own proof of `decide_eq_decide` goes through `propext`, so citing it
//! would cost this row its `axiom_closure: Empty`. Do not "simplify" the island
//! to use the prelude lemma without re-measuring the closure.
//! `~/a3d`'s conversion ledger (`crates/a3d-kernel/CONVERSION.md` §4, measured
//! 2026-09-19) names one open item and calls it "the single most valuable thing
//! left undone in this conversion":
//!
//! > `octree_depth_fits` proves that the Rust body is the decision `depth < 21`.
//! > It does not prove that 21 is the right number. The arithmetic that makes 21
//! > right — `3 * (20 + 1) < 64` and `¬(3 * (21 + 1) < 64)` — is stated and
//! > kernel-checked in the model (`octree_span_20_fits`,
//! > `octree_span_21_overflows`), and *nothing links the two*. Linking them needs
//! > a cited theorem of the form `depth_fits_isl d = span_fits_isl d`, i.e. an
//! > equality of two `Bool`-valued decisions over different predicates. It was
//! > attempted and did not go through: `simp` makes no progress on the goal and
//! > Clean has no `decide_congr`-class lemma to reach for.
//!
//! Both halves of that last sentence are TRUE and were re-measured on
//! `trustc 1.99.0-dev (379912412 2026-09-19)` before this row was written:
//!
//!   * `theorem l (d : UInt32) : depth_fits_isl d = span_fits_isl d := by simp`
//!     is rejected — ``Tactic failed: simp: no progress made on ⊢ Eq Bool
//!     (depth_fits_isl #F0) (span_fits_isl #F0)``;
//!   * `decide_eq_decide`, `Bool.decide_congr`, `decide_eq_true_eq` and
//!     `decide_eq_false_iff_not` are all `Unknown identifier` in this Clean's
//!     prelude. (`of_decide_eq_true`, `of_decide_eq_false` and
//!     `of_not_decide_eq_true` are present.)
//!
//! **The conclusion drawn from them was not.** The link is expressible TODAY,
//! with no toolchain change, because the congruence Lean core calls
//! `decide_eq_decide` (`Init/PropLemmas.lean:512`, leanprover/lean4
//! v4.30.0-rc2) is a plain `Decidable.rec` casework term that this Clean checks
//! as written. This row is that link, end to end, on the authenticated lane
//! that PUBLISHES. `r43` is its close negative twin (the guard's constant made
//! wrong, the honest link still cited) and `r44` is the Lean-side twin (the
//! link's own arithmetic made false).
//!
//! ============================================================================
//! SOURCE, AND WHAT WAS SIMPLIFIED
//! ============================================================================
//! Source: `<home>/a3d-wt-trust/crates/a3d-kernel/src/lib.rs:140` and
//! `src/kernel_model.lean:90` (read-only for this lane; nothing under `~/a3d`
//! or `~/a3d-wt-trust` was modified).
//!
//!     pub fn octree_depth_fits(depth: u32) -> bool
//!         ensures result == depth_fits_isl(depth)
//!     { depth < 21 }
//!
//! NOT SIMPLIFIED: the body, the carrier and `depth_fits_isl` are a3d's own,
//! character for character. What is ADDED is the second clause and the theorem
//! behind it.
//!
//! a3d's `octree_span_20_fits` / `octree_span_21_overflows` are two GROUND
//! facts (`3 * (20 + 1) < 64`, `¬(3 * (21 + 1) < 64)`). They pin the boundary
//! and nothing else, which is why they could not be cited: a contract needs a
//! statement about the WHOLE domain of `depth`. `span_fits_isl` below is that
//! statement — the same arithmetic, quantified — and the two ground facts are
//! its instances at 20 and 21, kept here so the row still states a3d's own
//! boundary in a3d's own spelling.
//!
//! ============================================================================
//! WHAT THIS ROW PINS
//! ============================================================================
//!   * `octree_depth_guard` — an UNCITED `ensures` naming the island decision,
//!     discharged by kernel definitional equality (wire solver
//!     `clean-kernel-defeq`). This is a3d's existing contract, unchanged.
//!   * `octree_depth_fits` — a CITED `ensures` whose Lean theorem proves the
//!     body's decision EQUALS a decision over a different predicate at a
//!     different carrier (wire solver `clean-kernel-citation`). This is the new
//!     capability.
//!
//! They are kept on SEPARATE functions on purpose. MEASURED 2026-09-20 on
//! 379912412: on a MIXED surface (one uncited and one cited clause on ONE
//! function) every row of that function is relabelled `clean-kernel-citation`
//! and `clean-kernel-defeq` disappears from the wire — which is deliberate
//! (`compiler/rustc_mir_transform/src/trust_verify.rs`: "on a mixed surface the
//! sealed authority records BOTH halves of the conjunction … and the row
//! carries the citation lane's solver label"), and would make this row's
//! `defeq=0` check fail for a reason that is not a defect. Anyone counting
//! `clean-kernel-defeq` rows in a crate should know that adding one cited
//! clause moves that function's defeq rows into the citation bucket.
//!
//! MEASURED on the packed toolchain built from `main` at 379912412b1, not
//! predicted: the raw `trustc -Ztrust-verify=on -O` lane reports
//! `4 proved, 0 failed, 0 unknown`, `of which 4 kernel-certified by the clean
//! CIC kernel`, and the JSON wire carries every row with
//! `assurance: Certified`, `axiom_closure: Empty`, `coverage: Unbounded`.
//! The publication facts (`Gate:`, the boundary line, `cited=`/`defeq=`) are
//! what this row's grader adds on top.
//!
//! COMMENTS INSIDE THE ISLAND ARE LEAN COMMENTS: `--` and `/- … -/`.

clean {
    -- ── The congruence Clean's prelude does not carry ──────────────────────
    --
    -- Lean 4 core, `Init/PropLemmas.lean:512` (leanprover/lean4 v4.30.0-rc2):
    --
    --   @[simp, bool_to_prop] theorem decide_eq_decide
    --       {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    --       decide p = decide q ↔ (p ↔ q)
    --
    -- Only the `mpr` direction is needed here, and it is written out rather
    -- than assumed: two nested `Decidable.casesOn`, four arms, no `propext`,
    -- no `Classical`, no axiom. That is why the wire rows below can report
    -- `axiom_closure: Empty`.
    theorem decide_eq_decide_mpr (p : Prop) (q : Prop)
        (dp : Decidable p) (dq : Decidable q) (h : Iff p q) :
        Eq (@Decidable.decide p dp) (@Decidable.decide q dq) :=
      Decidable.casesOn
        (motive := fun i => Eq (@Decidable.decide p i) (@Decidable.decide q dq)) dp
        (fun hnp =>
          Decidable.casesOn
            (motive := fun j => Eq Bool.false (@Decidable.decide q j)) dq
            (fun _ => Eq.refl Bool.false)
            (fun hq => False.elim (hnp (Iff.mpr h hq))))
        (fun hp =>
          Decidable.casesOn
            (motive := fun j => Eq Bool.true (@Decidable.decide q j)) dq
            (fun hnq => False.elim (hnq (Iff.mp h hp)))
            (fun _ => Eq.refl Bool.true))

    -- ── a3d's own guard decision, verbatim (kernel_model.lean:90) ──────────
    --
    -- A comparison against a LITERAL at an unsigned carrier must name its own
    -- decision instance; the `decide (d < 21)` sugar does not kernel-match the
    -- compiler's import of the body (a3d CONVERSION.md §4.2).
    def depth_fits_isl (d : UInt32) : Bool :=
      @Decidable.decide (LT.lt d (UInt32.ofNat 21))
                       (instDecidableUInt32Lt d (UInt32.ofNat 21))

    -- ── What makes 21 the RIGHT number ────────────────────────────────────
    --
    -- An octree of depth `d` addresses `3 * (d + 1)` bits. a3d's
    -- `octree_node_count` shifts by that width in `u64`, so the guard must
    -- admit exactly the depths for which `3 * (d + 1) < 64`. Stated at `Nat`,
    -- over the whole domain of `d` — not at `UInt32`, where `3 * (d + 1)`
    -- WRAPS and the two decisions genuinely differ (d = 1431655765 makes the
    -- UInt32 product 0).
    def span_fits_isl (d : UInt32) : Bool :=
      @Decidable.decide (Nat.lt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)
                       (Nat.decLt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)

    -- The machine carrier and the Nat carrier agree DEFINITIONALLY: UInt32's
    -- `<` is the `Nat` order on `toNat`, so both directions are the identity.
    theorem depth_carrier_iff (d : UInt32) :
        Iff (LT.lt d (UInt32.ofNat 21)) (Nat.lt (UInt32.toNat d) 21) :=
      Iff.intro (fun h => h) (fun h => h)

    -- n < 21  ->  3 * (n + 1) < 64.   `omega` cannot do this: it declines every
    -- goal whose Farkas certificate SCALES a hypothesis by a literal
    -- coefficient, and reports `close_goal rejected arithmetic proof: type
    -- mismatch: expected Nat.lt (Nat.mul 3 (Nat.add n 1)) 64, got
    -- Nat.le (Nat.succ n) 21` — it hands back the hypothesis as the goal's
    -- proof. (Measured 2026-09-20 on 379912412; `n < 21 |- n < 22` and
    -- `21 <= n |- 22 <= n + 1`, which need no scaling, both succeed.)
    theorem span_fwd (n : Nat) (h : Nat.lt n 21) :
        Nat.lt (Nat.mul 3 (Nat.add n 1)) 64 :=
      Nat.lt_of_le_of_lt (Nat.mul 3 (Nat.add n 1)) 63 64
        (Nat.mul_le_mul_left (Nat.add n 1) 21 3 h)
        (by decide)

    -- 3 * (n + 1) < 64  ->  n < 21, by the total split `Nat.le_or_lt`: above
    -- the cutoff the span is at least 66, which contradicts `< 64`.
    theorem span_bwd (n : Nat) (h : Nat.lt (Nat.mul 3 (Nat.add n 1)) 64) :
        Nat.lt n 21 :=
      Or.casesOn
        (motive := fun _ => Nat.lt n 21)
        (Nat.le_or_lt n 20)
        (fun hle20 => Nat.succ_le_succ hle20)
        (fun hge21 =>
          False.elim
            (Nat.lt_irrefl 66
              (Nat.lt_of_le_of_lt 66 (Nat.mul 3 (Nat.add n 1)) 66
                (Nat.mul_le_mul_left 22 (Nat.add n 1) 3 (Nat.succ_le_succ hge21))
                (Nat.lt_of_le_of_lt (Nat.mul 3 (Nat.add n 1)) 64 66
                  (Nat.le_of_lt h) (by decide)))))

    -- a3d's own two ground boundary facts, kept in a3d's spelling. They are the
    -- instances of `span_fwd` / `span_bwd` at the cutoff, and they are what a
    -- reader checks by eye.
    theorem octree_span_20_fits : Nat.lt (3 * (20 + 1)) 64 := by decide
    theorem octree_span_21_overflows : Not (Nat.lt (3 * (21 + 1)) 64) := by decide

    -- ── THE LINK ──────────────────────────────────────────────────────────
    --
    -- This is the statement a3d's CONVERSION.md §4 asks for, in its own
    -- spelling: `depth_fits_isl d = span_fits_isl d`. MEASURED: the unfolded
    -- form — `Eq (@Decidable.decide (LT.lt d (UInt32.ofNat 21)) (…)) (span_fits_isl d)`,
    -- which is what the compiler's E6 import of the body reduces to — also
    -- discharges the clause, with the identical `4 proved, 0 unknown`. The
    -- kernel delta-reduces the definition, so the readable form is enough;
    -- `r43` uses the unfolded one only because its island carries no
    -- `depth_fits_isl` to fold into.
    theorem depth_fits_is_span_fits : forall (d : UInt32),
        Eq (depth_fits_isl d) (span_fits_isl d) :=
      fun d =>
        decide_eq_decide_mpr
          (LT.lt d (UInt32.ofNat 21))
          (Nat.lt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)
          (instDecidableUInt32Lt d (UInt32.ofNat 21))
          (Nat.decLt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)
          (Iff.intro
            (fun h => span_fwd (UInt32.toNat d) (Iff.mp (depth_carrier_iff d) h))
            (fun h => Iff.mpr (depth_carrier_iff d) (span_bwd (UInt32.toNat d) h)))
}

/// a3d `octree_node_count`'s depth guard, UNCITED — a3d's contract, unchanged.
///
/// The clause proves this body IS the decision `depth < 21`. It says nothing
/// about whether 21 is the right cutoff; that is what `octree_depth_fits`
/// below adds.
pub fn octree_depth_guard(depth: u32) -> bool
    ensures result == depth_fits_isl(depth)
{
    depth < 21
}

/// The same guard, CITED against the arithmetic that fixes its constant.
///
/// The clause does not mention 21 at all. It says: this body admits exactly the
/// depths whose octree span `3 * (depth + 1)` fits in a 64-bit shift. Change the
/// 21 and the citation stops type-checking (`r43`); change the span bound and
/// the Lean side stops checking (`r44`).
pub fn octree_depth_fits(depth: u32) -> bool
    ensures result == span_fits_isl(depth) by depth_fits_is_span_fits
{
    depth < 21
}

fn main() {
    // Depth 20 is the last one a3d admits; 21 is the first it refuses. Both
    // functions agree, which is the run-time shadow of the clause above.
    let last_ok = (octree_depth_guard(20), octree_depth_fits(20));
    let first_bad = (octree_depth_guard(21), octree_depth_fits(21));
    let _ = (last_ok, first_bad);
}
