// A FULLY VERIFIED joint Rust+Lean program (2026-09-15): a Rust contract clause
// discharged by CITING a Lean theorem ABOUT the Lean (island) function the Rust
// body calls.
//
// `pb_max` is a Clean island definition; `pb_max_ge_left` is a kernel-checked
// tactic theorem about it. `pb_max_r` forwards to the island definition, so its
// body is E6-admitted as the defining equation `pb_max lhs rhs` and `result` in
// its postcondition DENOTES that term; the citation audit then re-checks the
// theorem's proof term against `∀ lhs rhs, lhs ≤ pb_max lhs rhs` — the clause
// over the compiler's encoding of the body — and the clause is kernel-certified
// (not solver-discharged, not Trusted). `shortfall_for`'s subtraction is then
// proved from the verified contract, so the whole program is 3 proved / 0 / 0
// under `-Ztrust-verify=on`, and it compiles under `-Ztrust-verify=off` too
// (the advisory citation sweep grades the same goal).
//
// The mismatched citation (`result >= rhs by pb_max_ge_left`) is the paired
// negative control, `tests/ui/trust/e9_joint_cited_island_theorem_mismatch.rs`:
// the same audit refuses it as a statement mismatch.
clean {
    def pb_max (lhs : UInt64) (rhs : UInt64) : UInt64 := if rhs < lhs then lhs else rhs
    theorem pb_max_ge_left (lhs rhs : UInt64) : lhs <= pb_max lhs rhs := by
      unfold pb_max
      split <;> omega
}

pub fn pb_max_r(lhs: u64, rhs: u64) -> u64
    ensures result >= lhs by pb_max_ge_left
{
    pb_max(lhs, rhs)
}

pub fn shortfall_for(lhs: u64, rhs: u64) -> u64 {
    pb_max_r(lhs, rhs) - lhs
}

fn main() {
    let s = shortfall_for(3, 10);
    let z = shortfall_for(10, 3);
    // No formatting machinery: `println!` routes through `std::io::_print`,
    // which is a separate (tolerated-gap) frontier — see r08/r09.
    assert!(s == 7);
    assert!(z == 0);
}
