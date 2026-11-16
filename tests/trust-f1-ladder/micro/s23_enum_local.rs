enum E { A, B(u64) }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let e = if x & 1 == 0 { E::A } else { E::B(x) }; match e { E::A => 5, E::B(v) => v + 1 } }
