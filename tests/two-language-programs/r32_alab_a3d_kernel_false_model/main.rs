//! CLOSE NEGATIVE TWIN of `r31`: the same a3d-kernel scalar core, the same two
//! functions, the same `targo trust check main.rs` invocation — and ONE changed
//! TOKEN in the Lean model. `within_isl` now decides `e < f` instead of
//! `e <= f`.
//!
//! WHY THIS PARTICULAR MUTATION. It is a real off-by-one in a real bounds
//! check, not a typo a reader spots. a3d's `range_in_bounds` documents a
//! HALF-OPEN range `[off, off + len)`: a read that ends exactly at EOF is in
//! bounds, so the decision is `end <= file_len`. The mutated model says a read
//! must stop strictly before EOF, which rejects every read of a file's last
//! byte — and agrees with the Rust body on every other input, so no test over
//! interior offsets separates them. It is exactly the shape of drift that
//! matters here: the code is RIGHT and the model is WRONG, which is the
//! direction a conversion actually fails in, because no test over interior
//! offsets separates them. Trust must refuse the pair rather than credit the
//! model.
//!
//! The owner has already paid for the OTHER direction:
//! `~/aterm/crates/aterm-spec-models/proofs/clean/ct_eq.lean` is the "ALGEBRAIC
//! CORE of the `constant_time_eq` length-fold bug (aterm 47cca4b)" — there the
//! CODE dropped delta bits above 2^16 and the model is the correct one, which
//! is why the file carries `buggySeed` beside `fixedSeed` with a theorem for
//! each. Both directions need the same machinery; only this one survives a test
//! suite, which is why the twin mutates the model.
//!
//! WHAT THE GRADER REQUIRES OF THIS ROW (`row_targo_file … refused`), and why
//! each part is here:
//!
//!   * exit non-zero and no `Gate: PASS` — the build is refused;
//!   * the compiler's own defeq refusal reaches the authenticated lane's log
//!     (`was not discharged by definitional equality`) — so the refusal is
//!     attributable to THIS clause and not to some unrelated breakage;
//!   * NO `[PROVED]` row under `clean-kernel-defeq` — the false model must not
//!     publish. A payload riding along with a discharge the kernel never made
//!     is the one failure the r29 evidence change could have introduced;
//!   * the honest CITED clause still publishes under `clean-kernel-citation` —
//!     `min_span` and its theorem are untouched, so a refusal that merely broke
//!     the whole run cannot be mistaken for a refusal of the false model.
//!
//! That last requirement is why r31 keeps its cited and uncited clauses on
//! SEPARATE functions: the conjunction rule declines a whole function when any
//! one of its `ensures` clauses has no kernel route, so a mixed surface here
//! would take the honest citation down with the false clause and the row could
//! not tell the two apart.
//!
//! READ THIS ROW WITH `r31`, NOT ALONE. The needle above
//! (`was not discharged by definitional equality`) is ALSO the head the
//! compiler formats for `CitationVerdict::ClauseOutsideFragment`
//! (`compiler/rustc_mir_transform/src/trust_verify.rs`), so a clause shape that
//! never reached the kernel on some future compiler would satisfy it too. A
//! green here beside a RED `r31` therefore means the shape broke, not that the
//! false model was caught. The same rule applies to the `r29`/`r30` pair.
//!
//! MEASURED on a stage1 built from this branch, not predicted: refused, exit 1,
//! on ``uncited `ensures` naming the Clean island definition `within_isl` was
//! not discharged by definitional equality``, with the honest cited clause still
//! publishing (`cited=3`). The control that says this green is the mutation's:
//! restoring `decide (e <= f)` turns the row into
//! `ACCEPTED a false Lean-discharged contract (exit 0)`.
//!
//! Source and simplifications: identical to `r31` — see its header.

clean {
    -- MUTATED: a3d's range is HALF-OPEN, so the honest decision is `e <= f`
    -- (r31). `e < f` rejects a read that ends exactly at end-of-file.
    def within_isl (e : UInt64) (f : UInt64) : Bool := decide (e < f)

    -- Untouched, and deliberately so: this is the honest half, and its
    -- citation must go on publishing.
    def min2_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b

    theorem min2_isl_le_left (a b : UInt64) : min2_isl a b <= a := by
      unfold min2_isl
      split <;> omega
}

/// The Rust body is a3d's, unchanged and CORRECT. The clause's second conjunct
/// now claims it agrees with a model that differs from it at `end == file_len`,
/// and the kernel's `Eq.refl` check must refuse that.
pub fn end_within_file(end: u64, file_len: u64) -> bool
    ensures result == (file_len >= end) && result == within_isl(end, file_len)
{
    end <= file_len
}

/// Honest, untouched: the refusal above must not cost this citation.
pub fn min_span(a: u64, b: u64) -> u64
    ensures result <= a by min2_isl_le_left
{
    if a < b { a } else { b }
}

fn main() {
    // The witness: a read ending exactly at EOF. The Rust body says `true`;
    // the mutated model says `false`.
    let ok = end_within_file(1048576, 1048576);
    let lo = min_span(7, 41);
    let _ = (ok, lo);
}
