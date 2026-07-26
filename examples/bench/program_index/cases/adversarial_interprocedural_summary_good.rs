// Adversarial fixture: callee summaries preserve a nonzero denominator guard.

fn denominator_is_nonzero(den: u32) -> bool {
    den != 0
}

fn branch_allows_division(enabled: bool, den: u32) -> bool {
    enabled && denominator_is_nonzero(den)
}

fn summarized_ratio(num: u32, den: u32, enabled: bool) -> u32 {
    if branch_allows_division(enabled, den) {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = summarized_ratio(18, 3, true);
    let _ = summarized_ratio(18, 0, true);
    let _ = summarized_ratio(18, 0, false);
}
