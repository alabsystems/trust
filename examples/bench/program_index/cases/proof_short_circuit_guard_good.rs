// Proof-design fixture: short-circuit guard preserves division safety.
//
// This stays free of formatting and allocation so the verifier sees the
// path-sensitive guard surface without std I/O noise.

fn divide_when_enabled(num: u32, den: u32, enabled: bool) -> u32 {
    if enabled && den != 0 {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = divide_when_enabled(12, 3, true);
    let _ = divide_when_enabled(12, 0, true);
    let _ = divide_when_enabled(12, 0, false);
}
