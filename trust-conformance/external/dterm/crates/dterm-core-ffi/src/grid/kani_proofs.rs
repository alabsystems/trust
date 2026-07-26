pub fn dterm_is_box_drawing_character(codepoint: u32) -> bool {
    matches!(codepoint, 0x2500..=0x257F)
}

#[cfg(feature = "kani-contracts")]
#[kani::proof_for_contract(dterm_is_box_drawing_character)]
fn dterm_is_box_drawing_character_contract() {
    let codepoint: u32 = kani::any();
    let _ = dterm_is_box_drawing_character(codepoint);
}
