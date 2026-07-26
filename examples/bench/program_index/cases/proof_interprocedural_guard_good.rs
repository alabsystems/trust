// Proof-design fixture: callee predicate guards a division.
//
// This stays free of formatting and allocation so the verifier sees the
// interprocedural proof surface without std I/O noise.

fn denominator_is_valid(den: u32) -> bool {
    den != 0
}

fn ratio_guarded(num: u32, den: u32) -> u32 {
    if denominator_is_valid(den) {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = ratio_guarded(12, 3);
    let _ = ratio_guarded(12, 0);
}
