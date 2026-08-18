#![warn(clippy::trust_hand_encoded_solver_query)]

/// The function `proofs/ay/` claims to certify. Nothing states the claim here,
/// so nothing re-derives it when this body changes.
fn keep_tail_chars(budget: u64) -> u64 {
    budget.min(4096)
}

fn main() {
    println!("{}", keep_tail_chars(9000));
}
