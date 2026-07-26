//@ battery-lane: A-rust
//@ battery-expect: frontier
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A FRONTIER — binary search: a correct loop the lane cannot execute
//! symbolically yet.
//!
//! The invariant and the measure are both true. `hi - lo` strictly decreases
//! every iteration and the bounds hold throughout. The obstacle is structural,
//! not mathematical: the E4/E5 loop-contract lane symbolically executes exactly
//! ONE body path — `single_path_loop_transition_blocks` walks from the body
//! target back to the header following only `Goto` and `Assert` terminators and
//! returns `None` on anything else. A three-way comparison compiles to two
//! `SwitchInt` terminators plus an extra loop exit (`return Some(mid)`), so
//! `symbolic_single_path_loop_transition` returns `None` and BOTH clauses push
//! `loop_contract_unsupported_vc`.
//!
//! ## MEASURED (2026-07-25, toolchain c6be27eb88): the gap CASCADES
//!
//! This file's verdict is `frontier-refuted`, and that is expected — it is a
//! standing alarm, deliberately left visible rather than relabelled away.
//!
//! The unsupported invariant does not merely go unproved. The obligations that
//! DEPEND on it are reported as FAILED:
//!
//!     help: guidance — must hold: the index must be provably `< len` at the
//!     access. | fix: check `i < slice.len()` before indexing
//!
//! `xs[mid]` is in bounds — `mid < hi <= xs.len()` follows directly from the
//! invariant. But because the invariant falls outside the single-path fragment,
//! the verifier proceeds as though it were absent, finds a state where the
//! index is unbounded, and refutes a TRUE obligation.
//!
//! That is a spurious failure, not a false accept — the direction that costs
//! trust rather than soundness. It is worth its own line in any report:
//! a fragment gap does not stay contained as an honest `unknown`; it degrades
//! into a wrong `failed` on everything downstream of it.
//!
//! Scored `frontier`, not `reject`: the tool did not refute these clauses, it
//! declined to model them. Binary search is close to the canonical example of
//! a program people expect a verifier to handle, which is exactly why this
//! belongs in the battery as a standing, visible measurement of the gap —
//! multi-path loop bodies are the single most valuable extension to the
//! loop-contract fragment.

/// Binary search over a sorted slice.
pub fn binary_search(xs: &[u32], key: u32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = xs.len();
    while lo < hi
        invariant lo <= hi && hi <= xs.len()
        decreases hi - lo
    {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < key {
            lo = mid + 1;
        } else if xs[mid] > key {
            hi = mid;
        } else {
            return Some(mid);
        }
    }
    None
}
