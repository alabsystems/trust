// Proof-design fixture: minimal flawed unreachable obligation.
//
// This stays free of formatting and allocation so the verifier sees the
// control-flow proof surface without std I/O noise.

fn classify_unchecked(x: u32) -> u32 {
    match x {
        0 => 0,
        1..=100 => 1,
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}

fn main() {
    let _ = classify_unchecked(50);
}
