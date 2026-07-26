// Adversarial fixture: std formatting behind a too-weak numeric guard.
//
// The main chooses passing inputs, but values from 10 through 99 falsify the
// assertion and should produce proof-strengthening evidence.

fn rendered_digit_len(value: u32) -> usize {
    let rendered = format!("value={}", value);
    if value < 100 {
        assert_eq!(rendered.len(), 7);
    }
    rendered.len()
}

fn main() {
    let _ = rendered_digit_len(3);
    let _ = rendered_digit_len(142);
}
