// Adversarial fixture: nested path guard preserves division safety.
//
// The good variant keeps the denominator guard on every path that can divide.

fn divide_for_tag(num: u32, den: u32, tag: u8) -> u32 {
    if tag == 7 {
        if den != 0 {
            num / den
        } else {
            0
        }
    } else {
        0
    }
}

fn main() {
    let _ = divide_for_tag(21, 3, 7);
    let _ = divide_for_tag(21, 0, 7);
    let _ = divide_for_tag(21, 0, 0);
}
