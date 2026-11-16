pub fn pct(part: u32, whole: u32) -> u32 {
    if whole == 0 { 0 } else { (part.min(whole) * 100) / whole }
}
