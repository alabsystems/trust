// Proof-design fixture: minimal flawed shift-overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// shift proof surface without std I/O noise.

fn shift_unchecked(x: u32, amount: u32) -> u32 {
    x << amount
}

fn main() {
    let _ = shift_unchecked(1, 4);
}
