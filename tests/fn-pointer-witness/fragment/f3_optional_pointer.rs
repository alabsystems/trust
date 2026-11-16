//@ fn-ptr-witness: refuses
//! THE SHARPEST ROW IN THE FRAGMENT, and the reason it is kept. This body
//! reports `1 proved, 0 failed, 0 unknown, 0 runtime-checked out of 1
//! obligation(s)` — a clean green — and carries NO `native-verification-gap`
//! row at all, unlike every other shape here. Its single proved row is
//! `kind: unreach`, "unreachable code reached": the `None` arm. The indirect
//! call `g()` is simply ABSENT from the inventory, with not even an `unknown`
//! row to hint at it.
//!
//! So a clean, fully-proved report is NOT evidence that an indirect call inside
//! the body was covered, and the gap row is not a reliable tripwire either. Two
//! successive drafts of this instrument were wrong here — the first asserted
//! `verifies` implies `no report`, the second asserted every shape carries an
//! `unknown` gap row. This row falsified both.
pub fn call(f: Option<fn()>) { if let Some(g) = f { g() } }
