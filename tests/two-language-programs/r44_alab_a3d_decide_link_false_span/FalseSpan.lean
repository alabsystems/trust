/- NEGATIVE TWIN of `r42`, on the LEAN side: the link's own arithmetic is
   false, and the kernel must refuse it.

   `r42` links a3d's guard decision `depth < 21` to the arithmetic that fixes
   its constant: the octree span `3 * (depth + 1)` must stay below a 64-bit
   shift width. ONE token changes here — the span bound `64` becomes `63` — and
   the two decisions stop being equivalent: depth 20 is admitted by the guard
   and refused by the span test (`3 * 21 = 63`, which is not `< 63`).

   This is the twin that pins the arithmetic itself. `r43` mutates the Rust body
   and is refused by the citation audit; this file never reaches Rust at all —
   the Lean declaration that carries the link's forward direction stops
   checking, and in a crate that would stop the build before any contract was
   considered.

   MEASURED 2026-09-20 on `targo 1.99.0-dev (379912412 2026-09-19)`:

     error: FalseSpan.lean:41:1: error: `span_fwd` did not elaborate:
            Tactic failed: decide: comparison is false
     REJECTED FalseSpan.lean

   The honest file is `r42`'s island, where the identical `span_fwd` with `64`
   kernel-checks. Read the two together: the refusal is one literal deep.

   WHY THE REFUSAL LANDS WHERE IT DOES. `span_fwd` chains
   `3 * (n + 1) <= 3 * 21 = 63` with `63 < BOUND`. At `BOUND = 64` the second
   step is the ground fact `63 < 64`; at `BOUND = 63` it is `63 < 63`, and
   `decide` reports the comparison false rather than inventing a proof. Nothing
   downstream is reached, which is the fail-closed behaviour this row pins. -/

def span_fits_isl (d : UInt32) : Bool :=
  @Decidable.decide (Nat.lt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 63)
                   (Nat.decLt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 63)

theorem depth_carrier_iff (d : UInt32) :
    Iff (LT.lt d (UInt32.ofNat 21)) (Nat.lt (UInt32.toNat d) 21) :=
  Iff.intro (fun h => h) (fun h => h)

/- THE MUTATION: the span bound is 63, not 64. `d < 21` and
   `3 * (d + 1) < 63` are not equivalent, so this must not check. -/
theorem span_fwd (n : Nat) (h : Nat.lt n 21) :
    Nat.lt (Nat.mul 3 (Nat.add n 1)) 63 :=
  Nat.lt_of_le_of_lt (Nat.mul 3 (Nat.add n 1)) 63 63
    (Nat.mul_le_mul_left (Nat.add n 1) 21 3 h)
    (by decide)
