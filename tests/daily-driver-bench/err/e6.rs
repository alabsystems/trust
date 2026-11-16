pub enum E { A, B } pub fn f(e: &E) -> u32 { match e { E::A => 1, E::B => 2 } }
