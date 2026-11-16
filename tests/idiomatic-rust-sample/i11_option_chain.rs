pub fn width(opt: Option<u32>) -> u32 { opt.map(|w| w.saturating_mul(2)).unwrap_or(0) }
