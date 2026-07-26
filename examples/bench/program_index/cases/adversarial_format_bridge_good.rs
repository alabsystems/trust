// Adversarial fixture: std formatting behind a correct numeric guard.
//
// This intentionally reaches formatter machinery so the std/format gap remains
// separate from formatter-free proof-design fixtures.

fn rendered_digit_len(value: u32) -> usize {
    let rendered = format!("value={}", value);
    if value < 10 {
        assert_eq!(rendered.len(), 7);
    }
    rendered.len()
}

fn main() {
    let _ = rendered_digit_len(3);
    let _ = rendered_digit_len(42);
}
