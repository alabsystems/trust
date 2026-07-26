// Proof-design fixture: minimal guarded addition-overflow obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// arithmetic proof surface without std I/O noise.

fn add_guarded(a: u32, b: u32) -> u32 {
    if a <= u32::MAX - b {
        a + b
    } else {
        u32::MAX
    }
}

fn main() {
    let _ = add_guarded(10, 3);
    let _ = add_guarded(u32::MAX, 1);
}
