pub fn res_chain(a: Result<u32, ()>) -> Result<u32, ()> {
    a.and_then(|x| if x > 0 { Ok(x) } else { Err(()) })
}
