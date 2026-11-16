pub fn g(a: u32) -> Result<u32, ()> { if a > 5 { Err(()) } else { Ok(a) } } pub fn f(a: u32) -> Result<u32, ()> { let b = g(a)?; Ok(b) }
