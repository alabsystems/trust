//@ battery-lane: A-rust
//@ battery-expect: frontier
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A FRONTIER — binary search: a correct loop whose path guards cross the
//! current one-principal-machine-domain boundary.
//!
//! The invariant and the measure are both true. `hi - lo` strictly decreases
//! every iteration and the bounds hold throughout. Bounded acyclic multi-path
//! execution is now implemented: both `SwitchInt` branches, the early return,
//! and all backedges are enumerated. The remaining obstacle is semantic rather
//! than topological. The invariant/measure use the `usize` domain, while path
//! guards compare `u32` elements (`xs[mid]`) with the `u32` key. E4/E5
//! deliberately refuse to reinterpret those guards at the `usize` width:
//! `e4.machine.mixed-domain` and `e5.machine.transition-translation` remain
//! visible until exact mixed-domain/cast transport lands.
//!
//! ## MEASURED (2026-07-26): the gap still cascades
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
//! invariant. But because the mixed-domain invariant cannot acquire proof
//! authority, the verifier proceeds as though it were absent, finds a state
//! where the index is unbounded, and refutes a TRUE obligation.
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
//! exact mixed-domain path assumptions and safe invariant reuse are the next
//! relevant extensions, not another CFG path walker.

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
