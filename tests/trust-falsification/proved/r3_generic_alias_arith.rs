#![crate_type = "lib"]
// Trust R3 (generics WIN W2): non-generic guarded arithmetic beside an opaque
// alias payload moved through an enum (the serde `Result<S::Ok, S::Error>`
// shape — `Option<S::Item>` here). Native lowering must COMPLETE (the payload
// field carries the pre-mono alias marker) and the T-independent `k + 1` must
// PROVE under its `k < 1000` guard. Pairs with the mutant (unguarded `k + 1`).
pub trait Src { type Item; }
pub fn r3_shift<S: Src>(pending: Option<S::Item>, k: u32) -> (Option<S::Item>, u32) {
    let bumped = if k < 1000 { k + 1 } else { 0 };
    (pending, bumped)
}
