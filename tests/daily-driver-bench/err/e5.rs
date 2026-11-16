pub fn f(a: u32) -> Result<u32, String> { if a > 5 { Err("big".to_string()) } else { Ok(a) } }
