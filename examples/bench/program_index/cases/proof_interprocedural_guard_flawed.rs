// Proof-design fixture: imprecise callee predicate fails to guard division.
//
// This stays free of formatting and allocation so the verifier sees the
// interprocedural proof surface without std I/O noise.

fn denominator_is_valid(_den: u32) -> bool {
    true
}

fn ratio_unchecked(num: u32, den: u32) -> u32 {
    if denominator_is_valid(den) {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = ratio_unchecked(12, 3);
}
