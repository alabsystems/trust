//! THE SECOND ALab REPO IN THE BATTERY: the constant-time comparator of
//! `~/aterm`, converted to the two-language surface and put through the
//! AUTHENTICATED lane (`targo trust check main.rs`) — the lane `r29`/`r31` pin,
//! with `r35` as its close negative twin.
//!
//! ============================================================================
//! SOURCE, AND WHAT WAS SIMPLIFIED
//! ============================================================================
//! Rust source: `~/aterm/crates/aterm-gui/src/control_auth.rs:427-444`
//! (read-only for this lane; nothing under `~/aterm` was modified).
//! Lean source: `~/aterm/crates/aterm-spec-models/proofs/clean/ct_eq.lean` —
//! the owner's own Clean model of the same function, written for the fix
//! `47cca4b`.
//!
//!     pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
//!         let max = a.len().max(b.len());
//!         let mut diff: u8 = u8::from(a.len() != b.len()) * 0xff;
//!         for i in 0..max {
//!             let av = *a.get(i).unwrap_or(&0);
//!             let bv = *b.get(i).unwrap_or(&0xff);
//!             diff |= av ^ bv;
//!         }
//!         diff == 0
//!     }
//!
//! The accumulator has two halves and `47cca4b` fixed one of them. This row
//! converts the two SCALAR facts that half rests on, and nothing else.
//!
//! SIMPLIFIED, and what each simplification costs:
//!
//!   * `u8::from(a.len() != b.len()) * 0xff` becomes the DECISION it computes,
//!     `a_len == b_len`. `u8::from` is a call and a select with CONSTANT arms
//!     is not admitted (measured: `tests/e6-fragment-probe/probes/f03_select_
//!     const_arms.rs`), so the 0x00/0xff encoding cannot be stated here. The
//!     predicate underneath it can, and it is the one the bug destroyed — the
//!     pre-47cca4b seed does not decide length equality at all (see `r35`).
//!     What this costs, said plainly: this row proves the comparator's length
//!     test agrees with the model. It says NOTHING about the byte fold, the
//!     `0`/`0xff` sentinel padding, or the constant-time property itself —
//!     none of which is in the admitted fragment, and the last of which is not
//!     a functional property at all and cannot be an `ensures`.
//!
//!   * `a.len().max(b.len())` becomes the select `if a_len < b_len { b_len }
//!     else { a_len }`. `u64::max` is a CALL and calls are outside the
//!     fragment; the select it expands to is a3d-style and is admitted. The
//!     property carried is the one the function's own doc comment states —
//!     "Always inspects every byte of the LONGER input (so length differences
//!     do not leak via early return)" — as `a_len <= result`.
//!
//!   * `a.len()` is `usize`, not `u64`. A `usize` binder WORKS (round 1) and
//!     the discharge lane resolves it to the target's fixed width before the
//!     elaborator sees it, so an island written over `UInt64` serves a `usize`
//!     contract on a 64-bit target — measured, both halves, in
//!     `crates/trust-certify/tests/alab_pilot_shapes.rs::
//!     boundary_usize_is_resolved_before_the_elaborator_sees_it`. This row
//!     keeps `u64` so that the pair r34/r35 varies in exactly one thing; the
//!     conversion guide §10c walks the `usize` spelling.
//!
//! WHAT THIS ROW DOES NOT CONVERT, and why it matters here more than in r31:
//! the OWNER'S LEAN FILE IS NOT CITED. `ct_eq.lean` states the same predicate
//! as `Nat.beq la lb` over `Nat`, and a `Nat`-level decision is NOT
//! definitionally equal to the machine carrier's decision instance — measured,
//! `alab_pilot_shapes.rs::boundary_the_nat_lift_closes_a_projection_and_
//! nothing_that_branches`. So this island RESTATES the predicate at `UInt64`
//! rather than importing the owner's. `r36` is the row that states a clause
//! over a `Nat`-level definition through the `as nat` lift — also UNCITED, and
//! also over a definition written for the fixture rather than taken from the
//! owner; its header says so in its first block. **No battery row cites an
//! owner's Lean file verbatim, in either repo.**
//!
//! Also not cited: `ct_eq.lean`'s two universally quantified theorems
//! (`fold_or_xor_zero_iff_eq`, `acc_zero_iff_len_and_bytes`) DO NOT CHECK.
//! Measured on the STANDALONE `clean 0.9.0` CLI, not on the embedded pin this
//! row runs against: `Checked 28 declarations ... 26 passed, 2 failed`, and the
//! two failures are exactly those theorems (invalid rewrite motive at
//! ct_eq.lean:180; `duplicate where-clause definition: s` at :241). Several of
//! their `where`-leaf lemmas cannot be type-correct in any checker (`:369-372`
//! returns `rfl` at a hypothesis type), so the general iff is not proved
//! anywhere; only the ground `rfl` witnesses hold. A contract that cited either
//! would earn nothing, so this row cites neither and states its own theorem.
//!
//! ============================================================================
//! WHAT THIS ROW PINS
//! ============================================================================
//!   * `lengths_agree` — an UNCITED `ensures` that calls a Clean island
//!     definition and closes by kernel definitional equality (wire solver
//!     `clean-kernel-defeq`). What is new here is the CONTRACT-DISCHARGE
//!     direction at `==`: `tests/ui/trust/e9_comparison_bool_discharge.rs`
//!     covers `<=`/`>=` only, and the island spelling that closes a `==` body
//!     — `decide (la = lb)`, through Clean's own `instDecidableEqUInt64` — was
//!     unmeasured before this row. `==` itself is NOT new to the battery:
//!     `r22_clean_bool_decide` already carries
//!     `def eqf (a : UInt64) (b : UInt64) : Bool := a == b` verified def-eq in
//!     the other direction (island definition to minted Rust fn), and records
//!     there that `==` emits `BEq.beq … a b`.
//!   * `scan_len` — a CITED `ensures` whose Lean theorem is re-checked against
//!     the compiler-elaborated goal (wire solver `clean-kernel-citation`).
//!
//! THE THEOREM IS A TERM PROOF, AND THAT IS FORCED. `r31` proves its bound with
//! `unfold; split <;> omega`. That tactic closes `min2 a b <= a`, whose arms are
//! `a ≤ a` and `b ≤ a` under `¬(a<b)` — and it DECLINES the mirror `min2 a b <=
//! b` and this row's `a <= max2 a b`, because each leaves a strict arm `a ≤ b`
//! under `a < b` at `UInt64`. Measured in
//! `alab_pilot_shapes.rs::boundary_omega_declines_the_strict_arm_of_a_uint64_select`;
//! the island is rejected with an `omega` internal reason, which does not tell
//! the author to restate the bound. The explicit `Decidable.casesOn` term
//! through `Nat.le_of_lt` recovers it. The shape is already in tree at
//! `tests/ui/trust/e9_requires_hypothesis_note.rs:52-54` — but copy only the
//! TERM from there: that theorem is proved UNDER its function's `requires`, and
//! since owner ruling OR-A1 (increment 1a) such a citation is credited only at
//! `Trusted` (`EnsuresCitationUnderRequiresDischarge`), which the authenticated
//! lane withholds — not the unconditional `Certified` discharge this row needs.
//!
//! COMMENTS INSIDE THE ISLAND ARE LEAN COMMENTS: `--` and `/- … -/`. `//` lexes
//! and then fails to parse, and the whole island is rejected.
//!
//! ============================================================================
//! EVIDENCE GRADE
//! ============================================================================
//! The island source, both clauses, both verdicts and both mutation controls
//! are MEASURED — `crates/trust-certify/tests/alab_pilot_shapes.rs`, which
//! drives the same public discharge path the compiler drives and asserts this
//! file's own text (`fixtures_carry_the_measured_island_text`).
//!
//! The BATTERY numbers are now MEASURED too. Run on stage1 built from this
//! branch (`trustc 1.99.0-dev (59429fd02 2026-09-18)`),
//! `tests/e2e_two_language_programs.sh --only r38_alab_aterm_ct_eq_seed`:
//!
//!     Gate: PASS [strict lane, exit 0] (5 proved, 0 failed, 0 runtime-checked,
//!     0 assumed, 0 mandated, 0 contract-pan; Publication boundary: 5
//!     obligation(s) passed the compiler, all 5 published (0 withheld);
//!     kernel rows proved: cited=3 defeq=2
//!
//! The two functions are kept on SEPARATE surfaces on purpose, for exactly
//! r31/r32's reason: `r35` mutates the model behind `lengths_agree` only, and
//! `scan_len`'s citation must go on publishing so the refusal cannot be
//! collateral damage.

clean {
-- aterm 47cca4b: the length seed is `0x00` when the lengths agree and `0xff`
-- when they do not, so the comparator is correct exactly when THIS predicate
-- is. `==` at an unsigned carrier goes through Clean's own
-- `instDecidableEqUInt64`, which is why the decision spells as `decide (la = lb)`.
def len_eq_isl (la : UInt64) (lb : UInt64) : Bool := decide (la = lb)

-- aterm `a.len().max(b.len())`: the number of byte positions the comparator
-- walks. DOCUMENTATION ONLY — no clause names it and the theorem below is
-- stated over the inline `if`, not over this definition (unlike r31, whose
-- theorem is `min2_isl a b <= a`). It is here so the shape being bounded is
-- readable; the kernel never sees it.
def scan_len_isl (la : UInt64) (lb : UInt64) : UInt64 := if la < lb then lb else la

-- Why the scan covers the first input, which its text never says. A TERM proof,
-- and that is forced: `split <;> omega` declines the strict arm at `UInt64`
-- (conversion guide, section 6.3b). `Decidable.casesOn` takes isFalse FIRST.
theorem scan_len_covers_left : forall (a : UInt64) (b : UInt64),
    Nat.le (UInt64.toNat a) (UInt64.toNat (if a < b then b else a)) :=
    fun a b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
            Nat.le (UInt64.toNat a) (UInt64.toNat (Decidable.casesOn
                (motive := fun _ => UInt64) d (fun _ => a) (fun _ => b))))
        (instDecidableUInt64Lt a b)
        (fun _ => Nat.le.refl (UInt64.toNat a))
        (fun h => Nat.le_of_lt h)
}

/// aterm's length seed, as the decision it computes: `47cca4b` seeds the
/// difference accumulator with `0x00` when the lengths agree and `0xff` when
/// they do not, so the comparator is correct exactly when this predicate is.
///
/// UNCITED: the clause names the island definition and the kernel closes it by
/// definitional equality against the E6 import of this body. The
/// `result == (a_len == b_len)` conjunct pairs the author's own operator with
/// the island's `decide`, so the clause states the stronger thing — that the
/// two are the SAME term, not merely equal at every input.
pub fn lengths_agree(a_len: u64, b_len: u64) -> bool
    ensures result == (a_len == b_len) && result == len_eq_isl(a_len, b_len)
{
    a_len == b_len
}

/// aterm's `a.len().max(b.len())`, as the select it expands to: the number of
/// byte positions the comparator walks.
///
/// CITED: the clause is the property `constant_time_eq`'s doc comment states
/// and its body's text does not — that the scan covers the FIRST input, so a
/// shorter `a` cannot end the loop early and leak its length. The Lean theorem
/// proves it.
pub fn scan_len(a_len: u64, b_len: u64) -> u64
    ensures a_len <= result by scan_len_covers_left
{
    if a_len < b_len { b_len } else { a_len }
}

fn main() {
    // A 64-hex-char token compared against itself, and against a token one
    // character short: the two cases aterm's auth path actually sees.
    let same = lengths_agree(64, 64);
    let differ = lengths_agree(64, 63);
    let walk = scan_len(64, 63);
    let _ = (same, differ, walk);
}
