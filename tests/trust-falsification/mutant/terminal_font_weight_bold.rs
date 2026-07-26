#![crate_type = "lib"]
// MUTANT: guard deleted — normalized+200 overflows near i32::MAX.
pub fn terminal_font_weight_bold(normalized: i32) -> i32 {
    normalized + 200
}
