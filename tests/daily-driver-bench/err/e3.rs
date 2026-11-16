pub fn f(x: Option<u32>) -> Result<u32, ()> { x.ok_or(()) }
