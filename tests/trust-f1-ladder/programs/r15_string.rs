#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let s = format!("{}-{}", x, x + 1); let mut t = String::from("ab"); t.push_str(&s); t.len() as u64 }
