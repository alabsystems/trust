// Adversarial fixture: strengthened branch guard blocks division by zero.
//
// This is the paired good target for backprop/proof-strengthening evidence.

fn guarded_quotient(num: u32, den: u32, enabled: bool) -> u32 {
    if enabled && den != 0 {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = guarded_quotient(30, 5, true);
    let _ = guarded_quotient(30, 0, true);
    let _ = guarded_quotient(30, 0, false);
}
