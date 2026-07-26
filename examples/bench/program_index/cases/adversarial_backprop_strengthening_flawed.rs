// Adversarial fixture: missing branch strengthening permits zero denominator.
//
// The main remains runtime-safe while the helper exposes a direct repair
// target: strengthen the enabled branch with den != 0.

fn guarded_quotient(num: u32, den: u32, enabled: bool) -> u32 {
    if enabled {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = guarded_quotient(30, 5, true);
    let _ = guarded_quotient(30, 0, false);
}
