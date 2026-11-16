pub fn port_or_default(s: &str) -> u32 { s.parse::<u32>().unwrap_or(8080) }
