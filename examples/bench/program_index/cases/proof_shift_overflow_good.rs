// Proof-design fixture: minimal guarded shift-overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// shift proof surface without std I/O noise.

fn shift_guarded(x: u32, amount: u32) -> u32 {
    if amount < 32 {
        x << amount
    } else {
        0
    }
}

fn main() {
    let _ = shift_guarded(1, 4);
    let _ = shift_guarded(1, 40);
}
