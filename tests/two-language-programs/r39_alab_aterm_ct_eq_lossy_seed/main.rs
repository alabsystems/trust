//! CLOSE NEGATIVE TWIN of `r34`, and the strongest one this battery has: the
//! false model is not a token a reviewer would spot, it is **aterm's own
//! shipped bug**, restored.
//!
//! Byte-for-byte `r34` except for the body of `len_eq_isl`. Where `r34` decides
//! `la = lb`, this decides the PRE-`47cca4b` seed:
//!
//!     let mut diff: u8 = (a.len() ^ b.len()) as u8
//!                      | ((a.len() ^ b.len()) >> 8) as u8;
//!
//! modelled exactly as the owner's own Clean file models it
//! (`~/aterm/crates/aterm-spec-models/proofs/clean/ct_eq.lean`, `buggySeed`):
//! `((la ^^^ lb) % 256) ||| (((la ^^^ lb) / 256) % 256)`, decided against zero.
//!
//! WHY THIS MUTATION. That seed folds only bits 0..16 of the length delta into
//! a `u8`. A delta whose set bits all lie at position >= 16 — that is, a
//! nonzero multiple of 65536 — leaves the seed 0, and with the SHORTER slice
//! first (so the padding sentinel is `unwrap_or(&0)` and the bytes are all
//! zero) the whole accumulator stays 0 and the comparator reports EQUAL on
//! UNEQUAL inputs. Argument order matters for the exploit and not for the
//! model: with the longer slice first, `b`'s `unwrap_or(&0xff)` sentinel
//! catches it anyway. `ct_eq.lean` carries the divergence as a kernel-checked
//! pair (`buggy_seed_drops_64k_delta : buggySeed 65536 0 = 0` beside
//! `fixed_seed_keeps_64k_delta : fixedSeed 65536 0 = 255`); `Nat.xor` is
//! symmetric, so the island's own claim is order-free.
//!
//! It agrees with the honest model on every length delta below 65536 — which
//! is why it survived aterm's test suite until someone went looking: the token
//! path uses fixed 64-hex-char lengths and never produces a 65536-aligned
//! delta.
//!
//! **A TEST CAN SEPARATE THEM — it just has to guess the witness first, and
//! that is the whole difference.** aterm found this after the fact and pinned
//! it by hand: `~/aterm/crates/aterm-gui/src/control_auth.rs`,
//! `constant_time_eq_detects_length_delta_above_16_bits`, which asserts
//! `!constant_time_eq(&vec![0u8; 64], &vec![0u8; 64 + 65536])` in both
//! argument orders and shipped with `47cca4b`, the commit this header cites
//! three times. The kernel separates the two models without anyone supplying
//! 65536, because definitional equality is not agreement on a sample.
//!
//! NOTE THE DIRECTION. `r32` mutates the MODEL against correct code (code
//! right, model wrong). This row is the OTHER direction made symmetric: the
//! model here is the one aterm actually shipped and the Rust body is the fixed
//! comparator, so the pair is exactly "the model has drifted behind the code".
//! Both directions must be refused, and both are.
//!
//! WHAT THE GRADER REQUIRES OF THIS ROW (`row_targo_file … refused`):
//!
//!   * exit non-zero and no `Gate: PASS`;
//!   * the compiler's own defeq refusal reaches the authenticated lane's log
//!     (`was not discharged by definitional equality`), so the refusal is
//!     attributable to THIS clause;
//!   * NO `[PROVED]` row under `clean-kernel-defeq` — the false model must not
//!     publish;
//!   * the honest CITED clause still publishes under `clean-kernel-citation`.
//!     `scan_len` and `scan_len_covers_left` are untouched, which is why the
//!     two functions are kept on separate surfaces (r31/r32's rule).
//!
//! READ THIS ROW WITH `r34`, NOT ALONE. The needle
//! (`was not discharged by definitional equality`) is also the head the
//! compiler formats for a clause that never reached the kernel, so a green here
//! beside a RED `r34` means the clause SHAPE broke on this compiler, not that
//! the false model was caught. Same rule as r29/r30 and r31/r32.
//!
//! THE ISLAND MUST STILL CHECK. If `Nat.lor`/`Nat.div`/`Nat.mod`/`Nat.xor` ever
//! stopped elaborating, this row would be refused at ISLAND REJECTION — a
//! different failure that the grader's needle would not see, and the row would
//! read green for the wrong reason. That it checks is measured:
//! `crates/trust-certify/tests/alab_pilot_shapes.rs::pin_r35_lossy_seed_island_checks`.
//!
//! EVIDENCE GRADE. The island, the clause, the refusal and the surviving
//! citation are MEASURED (`alab_pilot_shapes.rs::
//! neg_r35_lossy_seed_does_not_discharge_the_fixed_body` and
//! `pin_r35_cited_clause_survives_the_mutation`). The battery-level facts are
//! MEASURED too, on stage1 built from this branch
//! (`trustc 1.99.0-dev (59429fd02 2026-09-18)`),
//! `tests/e2e_two_language_programs.sh --only r39_alab_aterm_ct_eq_lossy_seed`:
//!
//!     refused on the false clause (exit 1, honest cited rows still
//!     published: 3): error: uncited `ensures` naming the Clean island
//!     definition `len_eq_isl` was not discharged by definitional equality:
//!     the two sides …
//!
//! — so the refusal names THIS clause, `defeq == 0`, and the honest citation
//! went on publishing.
//!
//! THE CONTROL THAT SAYS THIS GREEN IS THE MUTATION'S, and it was RUN
//! (2026-09-18, same stage1): restoring `decide (la = lb)` and re-running this
//! row prints
//!
//!     r39_alab_aterm_ct_eq_lossy_seed  targo-file  FAIL
//!     ACCEPTED a false Lean-discharged contract (exit 0): Gate: PASS
//!     [strict lane, exit 0] (5 proved, 0 failed, …)
//!
//! so this row's green is the mutation's and not the grader's default.
//!
//! Source and simplifications: identical to `r34` — see its header.

clean {
-- MUTATED, and the mutation is aterm's own pre-47cca4b seed:
--   (d % 256) ||| ((d / 256) % 256)  with  d = la XOR lb,  decided against 0.
-- Bits of the delta at position >= 16 are dropped, so two inputs whose lengths
-- differ by a nonzero multiple of 65536 read as EQUAL. r34 has `decide (la = lb)`.
def len_eq_isl (la : UInt64) (lb : UInt64) : Bool :=
    Nat.beq (Nat.lor (Nat.mod (Nat.xor (UInt64.toNat la) (UInt64.toNat lb)) 256)
                     (Nat.mod (Nat.div (Nat.xor (UInt64.toNat la) (UInt64.toNat lb)) 256) 256))
            0

-- Untouched, and deliberately so: this is the honest half, and its citation
-- must go on publishing. DOCUMENTATION ONLY, as in r34: no clause names it and
-- the theorem is stated over the inline `if`.
def scan_len_isl (la : UInt64) (lb : UInt64) : UInt64 := if la < lb then lb else la

theorem scan_len_covers_left : forall (a : UInt64) (b : UInt64),
    Nat.le (UInt64.toNat a) (UInt64.toNat (if a < b then b else a)) :=
    fun a b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
            Nat.le (UInt64.toNat a) (UInt64.toNat (Decidable.casesOn
                (motive := fun _ => UInt64) d (fun _ => a) (fun _ => b))))
        (instDecidableUInt64Lt a b)
        (fun _ => @Nat.le.refl (UInt64.toNat a))
        (fun h => Nat.le_of_lt h)
}

/// The Rust body is aterm's FIXED comparator's length test, unchanged and
/// correct. The clause's second conjunct now claims it agrees with the seed
/// `47cca4b` removed, and the kernel's `Eq.refl` check must refuse that.
pub fn lengths_agree(a_len: u64, b_len: u64) -> bool
    ensures result == (a_len == b_len) && result == len_eq_isl(a_len, b_len)
{
    a_len == b_len
}

/// Honest, untouched: the refusal above must not cost this citation.
pub fn scan_len(a_len: u64, b_len: u64) -> u64
    ensures a_len <= result by scan_len_covers_left
{
    if a_len < b_len { b_len } else { a_len }
}

fn main() {
    // THE WITNESS, and it is aterm's own: two inputs whose lengths differ by
    // exactly 65536, shorter first — the order in which the pre-47cca4b
    // comparator actually false-accepted. The fixed length test says "not
    // equal"; the seed this island models drops the delta and says "equal".
    let witness = lengths_agree(0, 65536);
    let walk = scan_len(0, 65536);
    let _ = (witness, walk);
}
