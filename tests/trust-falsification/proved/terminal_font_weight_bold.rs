#![crate_type = "lib"]
// Real orca-core obligation (terminal_fonts.rs): normalized+200 is overflow-safe
// under the [100,900] font-weight guard.
pub fn terminal_font_weight_bold(normalized: i32) -> i32 {
    if normalized >= 100 && normalized <= 900 { normalized + 200 } else { 700 }
}
