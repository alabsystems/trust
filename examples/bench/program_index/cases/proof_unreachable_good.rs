// Proof-design fixture: minimal safe alternative to unreachable control flow.
//
// This stays free of formatting and allocation so the verifier sees the
// control-flow proof surface without std I/O noise.

fn classify_total(x: u32) -> u32 {
    match x {
        0 => 0,
        1..=100 => 1,
        _ => 2,
    }
}

fn main() {
    let _ = classify_total(0);
    let _ = classify_total(50);
    let _ = classify_total(500);
}
