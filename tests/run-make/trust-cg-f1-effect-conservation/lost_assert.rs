//! The 2026-10-01 review's end-to-end codegen reproducer for a LOST PANIC CHECK. Built with
//! `-Ztrust-ir-lower-mutate-rhs-effects` (TEST-ONLY: the field-store right-hand-side lane as it
//! was before ec8b51bb3b), the division that builds the opaque `Option` payload is skipped, its
//! division-by-zero `Assert` with it. Before the gate counted `Assert`s, the trust-ir frontend
//! COMPLETED `div_lost` (1/1): its trust-ir had no `Assert` left for the frontend's "refuse every
//! `Assert`" rule to see, and the review's linked program printed `div_lost(1, 0) returned 1`
//! where Rust panics with "attempt to divide by zero".
pub type P = Option<(u32, u32)>;

pub fn div_lost(x: u32, y: u32) -> u32 {
    let o: P = Some((x / y, 2));
    if let Some(_) = o { 1 } else { 0 }
}
