// Adversarial fixture: disjunctive path guard permits division by zero.
//
// The main keeps runtime execution safe while the helper remains flawed for
// callers with tag == 7 and den == 0.

fn divide_for_tag(num: u32, den: u32, tag: u8) -> u32 {
    if tag == 7 || den != 0 {
        num / den
    } else {
        0
    }
}

fn main() {
    let _ = divide_for_tag(21, 3, 7);
    let _ = divide_for_tag(21, 0, 0);
}
