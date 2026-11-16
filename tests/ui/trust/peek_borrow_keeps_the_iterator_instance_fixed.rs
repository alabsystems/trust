//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A `&mut` borrow of a `Peekable` used only by std `peek` does not
//! change how many items the instance yields: `peek` buffers the item `next`
//! returns. The borrow counted as an escape, so the loop had no trip count and the
//! counter was refuted at `usize::MAX` (sweep `q45`). The twin `_refused.rs`
//! passes the borrow to a function that resets the iterator.
//! Default policy only: under certify the std call's own absent-callee panic
//! aggregate (`Peekable::peek`/`next`) stays runtime-checked, a separate gap.
pub fn last_of_runs(v: &[u32]) -> usize {
    let mut it = v.iter().peekable();
    let mut runs = 0usize;
    while let Some(_) = it.next() {
        if it.peek().is_none() {
            runs += 1;
        }
    }
    runs
}
